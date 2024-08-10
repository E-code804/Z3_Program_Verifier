{-# LANGUAGE DeriveGeneric #-}
module PBT where 

import Syntax
import Printer
import DafnyParser
import WP
import Z3
import Control.Monad (liftM2, liftM3)
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

-- Basic Testing for IntDiv.dfy

-- This arbitrary instance did not work because it match with another arbitrary
-- instance 'instance (Arbitrary a, Arbitrary b) => Arbitrary (a, b)'
-- This generates a positive integer for `n` and any integer for `m`
-- instance Arbitrary (Int, Int) where
--   arbitrary = do
--     m <- arbitrary         -- m can be any integer
--     n <- arbitrary `suchThat` (> 0)  -- n must be positive
--     return (m, n)

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