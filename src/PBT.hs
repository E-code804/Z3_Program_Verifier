{-# LANGUAGE DeriveGeneric #-}
module PBT where 

import Syntax
import Printer
import DafnyParser
import WP
import qualified Parser as P
import Z3
import Eval
import Control.Monad (liftM2, liftM3)
import Data.Map (Map, (!?))
import qualified Data.Map as Map
import Control.Monad.State
import Control.Applicative
import GHC.Generics (Generic)
import Data.List
import qualified Data.List as List
import Test.HUnit ((~?=))
import qualified Test.HUnit
import Test.QuickCheck
  ( Arbitrary (..),
    Gen,
    OrderedList (..),
    Property,
    Testable (..),
    listOf,
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
    suchThat,
    counterexample,
    ioProperty
  )
import System.Process (readProcess)
import System.IO (openTempFile, hClose)
import System.Exit (exitFailure)
import Test.QuickCheck.Monadic (monadicIO, run, assert, stop)

add1 :: Int -> Int -> Int
add1 n1 n2 = n1 + n2

-- Correct way of asserting a property for quickChecking the reversal of a list
prop_Reverse :: [Int] -> Property
prop_Reverse xs = reverse (reverse xs) === xs

-- Filter the [Specification] part of Method for Requires
getRequiresPredicates :: Method -> [Predicate]
getRequiresPredicates (Method _ _ _ specs _) = [p | Requires p <- specs] 

-- Code for generating values for method parameters.
getParamTypes :: Method -> [Type]
getParamTypes (Method _ params _ _ _) = map snd params

-- Gen an arbitrary value based on "Type"
genValueForType :: Type -> Gen Value
genValueForType TInt = IntVal <$> arbitrary
genValueForType TBool = BoolVal <$> arbitrary
genValueForType TArrayInt = ArrayVal <$> listOf arbitrary

-- Gen values for the params of a method based on their types
genParamsForMethod :: Method -> Gen [Value]
genParamsForMethod method = mapM genValueForType $ getParamTypes method

methodParams :: Method -> [Binding]
methodParams (Method _ ins _ _ _) = ins

methodSpecs :: Method -> [Specification]
methodSpecs (Method _ _ _ specs _) = specs

-- Function to check preconditions of a method hold for given parameters.
pre :: Method -> [Value] -> Bool
pre (Method _ params _ specs _) vs = 
  if length params == length vs then
    let initialStore = Map.fromList $ zip (map fst params) vs in
    let requiresSpecs = [p | Requires p <- specs]
    in all (\ (Predicate e) -> evaluate e initialStore == Just (BoolVal True)) requiresSpecs
  else
    False

-- Function to check postconditions of a method holds after body executes.
post :: Method -> Store -> Bool
post (Method _ _ _ specs _) s =
  let ensuresSpecs = [p | Ensures p <- specs] in
    all (\ (Predicate e) -> evaluate e s == Just (BoolVal True)) ensuresSpecs

prop_m :: Method -> Property
prop_m m = 
  forAll (genParamsForMethod m) $ \vs ->
    pre m vs ==> 
      case exec m vs of
        Just s -> post m s
        _ -> False

checkPreWithZ3 :: Method -> [Value] -> IO Bool
checkPreWithZ3 method args = do
  let params = methodParams method
  if length params /= length args
    then return False
    else do
      let initStore = Map.fromList (zip (map fst params) args)
      let reqExpr = requires (methodSpecs method)
      -- Substitute parameters into requires
      let reqSubstExpr = foldr (\(n,v) e -> subst e n (Val v)) reqExpr (Map.toList initStore)
      let reqPred = Predicate reqSubstExpr
      convertAndCheck reqPred "temp_requires.smt2"

runIfPreHolds :: Method -> [Value] -> IO (Maybe Store)
runIfPreHolds method args = do
  preHolds <- checkPreWithZ3 method args
  if preHolds
    then return (exec method args)
    else return Nothing

checkPostWithZ3 :: Method -> Store -> IO Bool
checkPostWithZ3 method store = do
  let postExpr = ensures (methodSpecs method)
  let postSubstExpr = foldr (\(n,v) e -> subst e n (Val v)) postExpr (Map.toList store)
  let postPred = Predicate postSubstExpr
  convertAndCheck postPred "temp_ensures.smt2"

loadMethod :: FilePath -> IO Method
loadMethod fp = do
  result <- parseDafnyFile fp
  case result of
    Left err -> do
      putStrLn $ "Error parsing file: " ++ show err
      exitFailure
    Right m  -> return m

prop_methodCorrectness :: Method -> Property
prop_methodCorrectness method =
  forAll (genParamsForMethod method) $ \args ->
    -- Use ==> to discard the test if preconditions don't hold
    ioProperty $ do
      preHolds <- checkPreWithZ3 method args
      if not preHolds
        then return True  -- Return True here so that QuickCheck discards (treat as trivial success)
        else do
          maybeStore <- runIfPreHolds method args
          case maybeStore of
            Nothing -> return False
            Just store -> checkPostWithZ3 method store

prop_checkFile :: FilePath -> IO ()
prop_checkFile fp = do
  method <- loadMethod fp
  quickCheck (prop_methodCorrectness method)

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

