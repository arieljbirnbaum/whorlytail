{-# LANGUAGE OverloadedStrings #-}

module Whorlytail.PlanSpec (tests) where

import Data.Either (isLeft)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Word (Word64)
import Hedgehog (Gen, Property, assert, forAll, property, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertEqual, assertFailure, testCase, (@?=))
import Test.Tasty.Hedgehog (testProperty)
import Whorlytail.Plan

tests :: TestTree
tests =
  testGroup
    "Whorlytail.Plan"
    [ unitTests,
      propertyTests
    ]

-- Helpers

gid :: Word64 -> GoalId
gid = Uid

gdata :: Text -> GoalData
gdata t = GoalData {title = t, description = mempty}

expectRight :: (Show e) => Either e a -> IO a
expectRight (Right x) = pure x
expectRight (Left e) = assertFailure ("Expected Right, got Left: " <> show e)

expectLeft :: (Show a) => Either e a -> IO e
expectLeft (Left e) = pure e
expectLeft (Right x) = assertFailure ("Expected Left, got Right: " <> show x)

-- Unit tests

unitTests :: TestTree
unitTests =
  testGroup
    "unit"
    [ testCase "empty plan has no nextGoals" $
        nextGoals emptyPlan @?= Set.empty,
      testCase "cottage pie readiness progression" $ do
        let dinner = gid 1
            pie = gid 2
            salad = gid 3
            mash = gid 4
            filling = gid 5
            cookPotatoes = gid 6
            mashPotatoes = gid 7
            minceMeat = gid 8
            heatPan = gid 9
            searMeat = gid 10
            assemblePie = gid 11
            bakePie = gid 12
            washFruit = gid 13
            chopFruit = gid 14
            mixFruit = gid 15
            p0 =
              foldr
                (\(i, t) -> setGoal i (gdata t))
                emptyPlan
                [ (dinner, "Make dinner"),
                  (pie, "Make cottage pie"),
                  (salad, "Make fruit salad"),
                  (mash, "Make mash"),
                  (filling, "Make filling"),
                  (cookPotatoes, "Cook potatoes"),
                  (mashPotatoes, "Mash potatoes"),
                  (minceMeat, "Mince meat"),
                  (heatPan, "Heat pan"),
                  (searMeat, "Sear meat"),
                  (assemblePie, "Assemble pie"),
                  (bakePie, "Bake pie"),
                  (washFruit, "Wash fruit"),
                  (chopFruit, "Chop fruit"),
                  (mixFruit, "Mix fruit")
                ]
        p1 <-
          foldMRight
            setParent
            p0
            [ pie `Blocks` dinner,
              salad `Blocks` dinner,
              mash `Blocks` pie,
              filling `Blocks` pie,
              assemblePie `Blocks` pie,
              bakePie `Blocks` pie,
              cookPotatoes `Blocks` mash,
              mashPotatoes `Blocks` mash,
              minceMeat `Blocks` filling,
              heatPan `Blocks` filling,
              searMeat `Blocks` filling,
              washFruit `Blocks` salad,
              chopFruit `Blocks` salad,
              mixFruit `Blocks` salad
            ]
        p2 <-
          foldMRight
            addDependencyEdge
            p1
            [ cookPotatoes `Blocks` mashPotatoes,
              minceMeat `Blocks` heatPan,
              heatPan `Blocks` searMeat,
              mash `Blocks` assemblePie,
              filling `Blocks` assemblePie,
              assemblePie `Blocks` bakePie,
              washFruit `Blocks` chopFruit,
              chopFruit `Blocks` mixFruit
            ]
        nextGoals p2 @?= Set.fromList [cookPotatoes, minceMeat, washFruit]

        p3 <- expectRight (setState Completed cookPotatoes p2)
        nextGoals p3 @?= Set.fromList [mashPotatoes, minceMeat, washFruit]

        p4 <- expectRight (setState Completed mashPotatoes p3)
        nextGoals p4 @?= Set.fromList [mash, minceMeat, washFruit],
      testCase "rejects self-loop and multi-hop cycles" $ do
        let p0 = setGoal (gid 2) (gdata "B") $ setGoal (gid 1) (gdata "A") emptyPlan
        _ <- expectLeft (addDependencyEdge (gid 1 `Blocks` gid 1) p0)
        p1 <- expectRight (addDependencyEdge (gid 1 `Blocks` gid 2) p0)
        _ <- expectLeft (addDependencyEdge (gid 2 `Blocks` gid 1) p1)
        pure (),
      testCase "finishing a parent cascades Cancelled to unfinished descendants" $ do
        let p0 =
              setGoal (gid 3) (gdata "grandchild")
                $ setGoal (gid 2) (gdata "child")
                $ setGoal (gid 1) (gdata "parent") emptyPlan
        p1 <- expectRight (setParent (gid 2 `Blocks` gid 1) p0)
        p2 <- expectRight (setParent (gid 3 `Blocks` gid 2) p1)
        p3 <- expectRight (setState Completed (gid 1) p2)
        fmap snd (Map.lookup (gid 2) (goals p3)) @?= Just Cancelled
        fmap snd (Map.lookup (gid 3) (goals p3)) @?= Just Cancelled,
      testCase "rejects reopening a child under a finished parent" $ do
        let p0 = setGoal (gid 2) (gdata "child") $ setGoal (gid 1) (gdata "parent") emptyPlan
        p1 <- expectRight (setParent (gid 2 `Blocks` gid 1) p0)
        p2 <- expectRight (setState Completed (gid 1) p1)
        _ <- expectLeft (setState NeedsAction (gid 2) p2)
        pure (),
      testCase "reparenting keeps prior dependency edge" $ do
        let p0 =
              setGoal (gid 3) (gdata "p2")
                $ setGoal (gid 2) (gdata "p1")
                $ setGoal (gid 1) (gdata "c") emptyPlan
        p1 <- expectRight (setParent (gid 1 `Blocks` gid 2) p0)
        p2 <- expectRight (setParent (gid 1 `Blocks` gid 3) p1)
        Map.lookup (gid 1) (parents p2) @?= Just (gid 3)
        assertBool "old dependency edge kept" $
          Set.member (gid 2) (Map.findWithDefault Set.empty (gid 1) (blocks p2)),
      testCase "removeDependencyEdge unsets parent when removing parent edge" $ do
        let p0 = setGoal (gid 2) (gdata "p") $ setGoal (gid 1) (gdata "c") emptyPlan
        p1 <- expectRight (setParent (gid 1 `Blocks` gid 2) p0)
        let p2 = removeDependencyEdge (gid 1 `Blocks` gid 2) p1
        Map.lookup (gid 1) (parents p2) @?= Nothing,
      testCase "removals are idempotent on missing goals and edges" $ do
        let p0 = setGoal (gid 1) (gdata "A") emptyPlan
        assertEqual "removeGoal missing" p0 (removeGoal (gid 99) p0)
        assertEqual "unsetParent missing" p0 (unsetParent (gid 99) p0)
        assertEqual "removeDependencyEdge missing" p0 (removeDependencyEdge (gid 1 `Blocks` gid 99) p0)
        assertBool "addDependencyEdge missing goal fails" $
          isLeft (addDependencyEdge (gid 1 `Blocks` gid 99) p0)
    ]

foldMRight :: (Show e) => (a -> s -> Either e s) -> s -> [a] -> IO s
foldMRight _ s [] = pure s
foldMRight f s (x : xs) = expectRight (f x s) >>= \s' -> foldMRight f s' xs

-- Property tests (Lean spec invariants)

data Op
  = OpSetGoal GoalId Text
  | OpRemoveGoal GoalId
  | OpAddDep DependencyEdge
  | OpRemoveDep DependencyEdge
  | OpSetParent DependencyEdge
  | OpUnsetParent GoalId
  | OpSetState GoalState GoalId
  deriving (Show)

genGoalId :: Gen GoalId
genGoalId = Uid <$> Gen.word64 (Range.linear 1 8)

genGoalState :: Gen GoalState
genGoalState = Gen.element [NeedsAction, InProgress, Completed, Cancelled]

genEdge :: Gen DependencyEdge
genEdge = Blocks <$> genGoalId <*> genGoalId

genOp :: Gen Op
genOp =
  Gen.choice
    [ OpSetGoal <$> genGoalId <*> Gen.text (Range.linear 0 8) Gen.alphaNum,
      OpRemoveGoal <$> genGoalId,
      OpAddDep <$> genEdge,
      OpRemoveDep <$> genEdge,
      OpSetParent <$> genEdge,
      OpUnsetParent <$> genGoalId,
      OpSetState <$> genGoalState <*> genGoalId
    ]

applyOp :: Op -> PlanState -> PlanState
applyOp op p = case op of
  OpSetGoal g t -> setGoal g (gdata t) p
  OpRemoveGoal g -> removeGoal g p
  OpAddDep e -> either (const p) id (addDependencyEdge e p)
  OpRemoveDep e -> removeDependencyEdge e p
  OpSetParent e -> either (const p) id (setParent e p)
  OpUnsetParent g -> unsetParent g p
  OpSetState st g -> either (const p) id (setState st g p)

reachableFrom :: Map.Map GoalId (Set GoalId) -> GoalId -> Set GoalId
reachableFrom adj start = go Set.empty (Set.toList (Map.findWithDefault Set.empty start adj))
  where
    go visited [] = visited
    go visited (x : xs)
      | Set.member x visited = go visited xs
      | otherwise =
          let nexts = Set.toList (Map.findWithDefault Set.empty x adj)
           in go (Set.insert x visited) (nexts <> xs)

invariantsHold :: PlanState -> Bool
invariantsHold p =
  let gs = Map.keysSet (goals p)
      bs = blocks p
      ps = parents p
      blocksEndpointsValid =
        all (\(a, outs) -> Set.member a gs && Set.isSubsetOf outs gs) (Map.toList bs)
      parentsSubgraphOfBlocks =
        all (\(c, par) -> Set.member par (Map.findWithDefault Set.empty c bs)) (Map.toList ps)
      acyclic =
        all (\g -> not (Set.member g (reachableFrom bs g))) (Set.toList gs)
      noPendingChildren =
        all
          ( \(c, par) ->
              case (Map.lookup par (goals p), Map.lookup c (goals p)) of
                (Just (_, parSt), Just (_, cSt)) -> not (isFinished parSt) || isFinished cSt
                _ -> False
          )
          (Map.toList ps)
   in blocksEndpointsValid && parentsSubgraphOfBlocks && acyclic && noPendingChildren

expectedNextGoals :: PlanState -> Set GoalId
expectedNextGoals p =
  let unfinished = Set.fromList [g | (g, (_, st)) <- Map.toList (goals p), not (isFinished st)]
      blockedByUnfinished =
        Set.unions [reachableFrom (blocks p) u | u <- Set.toList unfinished]
   in Set.difference unfinished blockedByUnfinished

propertyTests :: TestTree
propertyTests =
  testGroup
    "properties"
    [ testProperty "all Lean invariants hold after arbitrary operation sequences" $
        propInvariants,
      testProperty "nextGoals matches spec and satisfies progress (no deadlock)" $
        propNextGoalsAndProgress
    ]

propInvariants :: Property
propInvariants = property $ do
  ops <- forAll (Gen.list (Range.linear 0 60) genOp)
  let states = scanl (flip applyOp) emptyPlan ops
  assert (all invariantsHold states)

propNextGoalsAndProgress :: Property
propNextGoalsAndProgress = property $ do
  ops <- forAll (Gen.list (Range.linear 0 60) genOp)
  let p = foldl (flip applyOp) emptyPlan ops
      ng = nextGoals p
      hasUnfinished = any (not . isFinished . snd) (Map.elems (goals p))
  ng === expectedNextGoals p
  assert (not hasUnfinished || not (Set.null ng))