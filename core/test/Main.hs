module Main (main) where

import Test.Tasty (defaultMain, testGroup)
import Whorlytail.PlanSpec qualified as PlanSpec

main :: IO ()
main = defaultMain $ testGroup "whorlytail-core" [PlanSpec.tests]