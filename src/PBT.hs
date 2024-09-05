{-# LANGUAGE DeriveGeneric #-}
module PBT where 

import Syntax
import Printer
import DafnyParser
import WP
import Z3
import Eval
import Control.Monad (liftM2, liftM3)
import Control.Monad.State
import Control.Applicative
import GHC.Generics (Generic)
import qualified Data.List as List
import Test.HUnit ((~?=))
import qualified Test.HUnit
import Test.QuickCheck
  ( Arbitrary (..),
    Gen,
    OrderedList (..),
    Property,
    Testable (..),
    choose,
    classify,
    elements,
    forAll,
    frequency,
    label,
    oneof,
    quickCheck,
    sample,
    sized,
    withMaxSuccess,
    (==>),
    (===),
    collect,
    genericShrink,
    suchThat
  )

add1 :: Int -> Int -> Int
add1 n1 n2 = n1 + n2

-- Correct way of asserting a property for quickChecking the reversal of a list
prop_Reverse :: [Int] -> Property
prop_Reverse xs = reverse (reverse xs) === xs






-- Filter the [Specification] part of Method for Requires
getRequiresPredicates :: Method -> [Predicate]
getRequiresPredicates (Method _ _ _ specs _) = [p | Requires p <- specs]

-- Evalute Predicates.
evalPredicate :: Predicate -> Eval Value
evalPredicate (Predicate expr) = evalE expr

-- Should be prop here? Checking if predicate holds
predHolds :: Predicate -> Store -> Bool
predHolds p store = case evalStateT (evalPredicate p) store of
  Just (BoolVal True) -> True
  _                   -> False

-- Example usage: 
-- let preds = getRequiresPredicates wLoopToZero
-- runTests preds initialStore
-- AS OF NOW, outputs: *** Failed! Falsified (after 1 test): 
runTests :: [Predicate] -> Store -> IO ()
runTests preds store = mapM_ (\p -> quickCheck (predHolds p store)) preds
-- getPredicate :: [Specification] -> 

-- testMethod :: Method -> Property


-- Basic Testing for IntDiv.dfy

-- Needed to make a newtype wrapper to avoid conflict.
newtype MyIntPair = MyIntPair (Int, Int) deriving Show

instance Arbitrary MyIntPair where
  arbitrary = do
    m <- arbitrary
    n <- arbitrary `suchThat` (> 0)
    return $ MyIntPair (m, n)

-- Property using the newtype
prop_IntDivValidInputs :: MyIntPair -> Bool
prop_IntDivValidInputs (MyIntPair (m, n)) =
  n > 0 && (m == (d * n + r)) && (0 <= r) && (r < n)
  where
    d = m `div` n
    r = m `mod` n