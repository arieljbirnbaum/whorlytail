module Whorlytail.Plan
  ( GoalId,
    GoalData (..),
    GoalState (..),
    PlanState,
    DependencyEdge (..),
    Uid (..),
    isFinished,
    goals,
    blocks,
    parents,
    emptyPlan,
    setGoal,
    removeGoal,
    addDependencyEdge,
    removeDependencyEdge,
    setParent,
    unsetParent,
    setState,
    nextGoals,
  )
where

import Algebra.Graph.AdjacencyMap qualified as AM
import Algebra.Graph.AdjacencyMap.Algorithm (reachable)
import Control.Monad (MonadPlus, guard, unless)
import Data.Bifunctor (first)
import Data.Functor (($>))
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Word (Word64)

newtype Uid a = Uid Word64 deriving (Eq, Ord, Show)

data Goal

type GoalId = Uid Goal

data GoalData = GoalData
  { title :: Text,
    description :: Text
  }
  deriving (Eq, Show)

data GoalState
  = NeedsAction
  | InProgress
  | Completed
  | Cancelled
  deriving (Eq, Show)

isFinished :: GoalState -> Bool
isFinished Completed = True
isFinished Cancelled = True
isFinished NeedsAction = False
isFinished InProgress = False

data PlanState = Plan
  { goals :: Map GoalId (GoalData, GoalState),
    blocks :: Map GoalId (Set GoalId), -- Acyclic directed graph on goals
    parents :: Map GoalId GoalId -- Directed graph on goals; subgraph of blocks (child blocks parent)
  }
  deriving (Eq, Show)

emptyPlan :: PlanState
emptyPlan =
  Plan
    { goals = Map.empty,
      blocks = Map.empty,
      parents = Map.empty
    }

data DependencyEdge = GoalId `Blocks` GoalId
  deriving (Eq, Show)

infixr 5 :§

type (:§) = Either

-- Set the data for a goal, creating it if it doesn't exist
setGoal :: GoalId -> GoalData -> PlanState -> PlanState
setGoal goalId goalData planState =
  planState
    { goals =
        Map.alter
          ( \m -> case m of
              Nothing -> Just (goalData, NeedsAction)
              Just (_, st) -> Just (goalData, st)
          )
          goalId
          (goals planState)
    }

validate :: (MonadPlus m) => (a -> Bool) -> a -> m a
validate p a = guard (p a) $> a

-- Remove a goal (idempotent)
removeGoal :: GoalId -> PlanState -> PlanState
removeGoal goalId planState =
  planState
    { goals = Map.delete goalId (goals planState),
      blocks =
        Map.mapMaybe (validate (not . Set.null) . Set.delete goalId)
          . Map.delete goalId
          $ blocks planState,
      parents =
        Map.filter (/= goalId)
          . Map.delete goalId
          $ parents planState
    }

data DependencyCycleError = DependencyCycle [DependencyEdge]
  deriving (Eq, Show)

data GoalNotFoundError = GoalNotFound GoalId
  deriving (Eq, Show)

blocksAM :: Map GoalId (Set GoalId) -> AM.AdjacencyMap GoalId
blocksAM = AM.fromAdjacencySets . Map.toList

insertBlock :: GoalId -> GoalId -> Map GoalId (Set GoalId) -> Map GoalId (Set GoalId)
insertBlock from to = Map.insertWith Set.union from (Set.singleton to)

-- Vertex path from start to target in the existing blocks graph (inclusive), if any.
findPath :: GoalId -> GoalId -> Map GoalId (Set GoalId) -> Maybe [GoalId]
findPath start target m
  | start == target = Just [start]
  | otherwise = go Set.empty [(start, [start])]
  where
    go _ [] = Nothing
    go visited ((x, path) : rest)
      | Set.member x visited = go visited rest
      | otherwise =
          let visited' = Set.insert x visited
              nexts = Set.toList (Map.findWithDefault Set.empty x m)
           in case filter (== target) nexts of
                (t : _) -> Just (reverse (t : path))
                [] ->
                  go
                    visited'
                    (rest ++ [(n, n : path) | n <- nexts, not (Set.member n visited')])

-- Full cycle that would appear if blocker→blocked were added.
cycleWitness :: GoalId -> GoalId -> Map GoalId (Set GoalId) -> Maybe [DependencyEdge]
cycleWitness blocker blocked m
  | blocker == blocked = Just [blocker `Blocks` blocked]
  | otherwise = do
      path <- findPath blocked blocker m
      pure (zipWith Blocks path (drop 1 path) ++ [blocker `Blocks` blocked])

-- Add a dependency edge between two goals
addDependencyEdge :: DependencyEdge -> PlanState -> Either (GoalNotFoundError :§ DependencyCycleError) PlanState
addDependencyEdge (blocker `Blocks` blocked) planState = do
  unless (Map.member blocker (goals planState)) $
    Left (Left (GoalNotFound blocker))
  unless (Map.member blocked (goals planState)) $
    Left (Left (GoalNotFound blocked))
  case cycleWitness blocker blocked (blocks planState) of
    Just edges -> Left (Right (DependencyCycle edges))
    Nothing ->
      Right
        planState
          { blocks = insertBlock blocker blocked (blocks planState)
          }

-- Remove a dependency edge between two goals (idempotent)
removeDependencyEdge :: DependencyEdge -> PlanState -> PlanState
removeDependencyEdge (blocker `Blocks` blocked) planState =
  planState
    { blocks = Map.update (validate (not . Set.null) . Set.delete blocked) blocker (blocks planState),
      parents = case Map.lookup blocker (parents planState) of
        Just p | p == blocked -> Map.delete blocker (parents planState)
        _ -> parents planState
    }

data FinishedParentWithUnfinishedChildError = UnfinishedChild DependencyEdge
  deriving (Eq, Show)

type SetParentError = GoalNotFoundError :§ FinishedParentWithUnfinishedChildError :§ DependencyCycleError

-- Set the parent of a goal
setParent :: DependencyEdge -> PlanState -> Either SetParentError PlanState
setParent edge@(child `Blocks` parent) planState = do
  case (Map.lookup child (goals planState), Map.lookup parent (goals planState)) of
    (Just (_, cSt), Just (_, pSt))
      | not (isFinished cSt) && isFinished pSt ->
          Left (Right (Left (UnfinishedChild edge)))
    _ -> pure ()
  plan' <- first (fmap Right) (addDependencyEdge edge planState)
  pure plan' {parents = Map.insert child parent (parents plan')}

-- Remove the parent of a goal (idempotent)
unsetParent :: GoalId -> PlanState -> PlanState
unsetParent goalId planState =
  planState {parents = Map.delete goalId (parents planState)}

type SetStateError = GoalNotFoundError :§ FinishedParentWithUnfinishedChildError

childrenOf :: GoalId -> Map GoalId GoalId -> [GoalId]
childrenOf parentId ps =
  [c | (c, p) <- Map.toList ps, p == parentId]

cancelUnfinishedDescendants :: GoalId -> Map GoalId (GoalData, GoalState) -> Map GoalId GoalId -> Map GoalId (GoalData, GoalState)
cancelUnfinishedDescendants root gs ps = go (childrenOf root ps) gs
  where
    go [] acc = acc
    go (c : cs) acc =
      case Map.lookup c acc of
        Just (gd, st)
          | not (isFinished st) ->
              go (childrenOf c ps ++ cs) (Map.insert c (gd, Cancelled) acc)
        _ -> go (childrenOf c ps ++ cs) acc

-- Set the state of a goal
-- Note: Finishing a parent cancels its children
setState :: GoalState -> GoalId -> PlanState -> Either SetStateError PlanState
setState newState goalId planState = do
  (gd, _) <- maybe (Left (Left (GoalNotFound goalId))) Right (Map.lookup goalId (goals planState))
  unless (isFinished newState) $
    case Map.lookup goalId (parents planState) of
      Just par
        | Just (_, pSt) <- Map.lookup par (goals planState),
          isFinished pSt ->
            Left (Right (UnfinishedChild (goalId `Blocks` par)))
      _ -> pure ()
  let goals' = Map.insert goalId (gd, newState) (goals planState)
      goals''
        | isFinished newState = cancelUnfinishedDescendants goalId goals' (parents planState)
        | otherwise = goals'
  pure planState {goals = goals''}

-- Return all unfinished goals not blocked (transitively) by other unfinished goals
nextGoals :: PlanState -> Set GoalId
nextGoals plan =
  let unfinished =
        Set.fromList
          [g | (g, (_, st)) <- Map.toList (goals plan), not (isFinished st)]
      am = blocksAM (blocks plan)
      blockedByUnfinished =
        Set.unions
          [ Set.fromList (reachable am u) Set.\\ Set.singleton u
          | u <- Set.toList unfinished
          ]
   in unfinished Set.\\ blockedByUnfinished
