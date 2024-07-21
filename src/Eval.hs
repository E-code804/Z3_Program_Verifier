{- | An Interpreter for MiniDafny |
   ================================

In this problem, you will use the state monad to build an *interpreter* and a stepper for
our simple imperative language.

-}
-- 02424R
module Eval where

{- |
This assignment uses the State Monad module from the standard library.

Because the MiniDafny language includes variables, we'll also use the finite
 maps from Haskell's containers library (Data.Map) to represent the store.

-}

import Control.Monad (when)
import Data.Map (Map, (!?))
import qualified Data.Map as Map
import Control.Monad.State
import Test.HUnit (Test(..), (~?=), (~:), runTestTT, Counts)
import qualified Data.List as List
import Data.Maybe (fromMaybe)
import Text.Read(readMaybe)
import Syntax

{- | The MiniDafny Store |
   -----------------------

One component of the interpreter is a *store* that represents our computer's
memory or heap during the evaluation of MiniDafny prorams. We represent this store
as an associative map from variable `Name`s to `Values`:

-}

type Store = Map Name Value

{- | When the evaluator starts, the initial store will be empty,
and will be updated with any variables passed in as arguments
before evaluating a method.
-}

initialStore :: Store
initialStore = Map.empty

{- |
During computation, the store could be extended to include new mappings for
global variables. For example, if we called a method with a 
parameter "x" with the integer 3, a parameter "a" corresponding to the array
with elements from one to four, and then allocated a new local variable
"y" with the value `True`, then the store will look like this:

-}

extendedStore :: Store
extendedStore = Map.fromList [("x", IntVal 3),
                              ("a", ArrayVal [1,2,3,4]),
                              ("y", BoolVal True)]

-- | Any store can be pretty-printed and displayed concisely using 
-- | your pretty printers.


-- | We will be using the StateT transformer from the standard library
-- | to encode the type of our evaluator: it needs State to access the
-- | Store and wraps results in a Maybe to gracefully handle errors.

type Eval = StateT Store Maybe

{- |  
We can use the name of a variable to find out its value 
or update it in an assignment.

First, let's write a function that looks up values from the store. If
a variable doesn't exist, this function can error. Remember:
in regular Dafny variables must be initialized, but since we haven't implemented
those checks in MiniDafny, you can't assume here that they have already happened.
-}

index :: Name -> Eval Value
index n = do
   s <- get
   lift $ Map.lookup n s

test_index :: Test
test_index = "index tests" ~: TestList [ 
   -- The global variable "x" is unitialized (i.e. not present in the initial store)
   evalStateT (index "x") initialStore  ~?= Nothing,
   -- But there is a value for "x" available in the extended store
   evalStateT (index "x") extendedStore ~?= Just (IntVal 3)
   ]

{- | 
We can also update values in the store. If the variable name doesn't already
exist in the store, it should be added. Otherwise, it should modify
the store according to the new association.
-}

update :: Name -> Value -> Eval ()
update n v = do
   s <- get
   put $ Map.insert n v s

test_update :: Test
test_update = "update tests" ~: TestList [
   -- If we assign to x, then we can find its new value
   evalStateT (update "x" (IntVal 4) >> index "x") initialStore ~?= Just (IntVal 4),
   -- If we assign to x, then we can find its new value
   evalStateT (update "x" (IntVal 5) >> index "x") extendedStore ~?= Just (IntVal 5),
   -- If we assign to y, then we can't find a value for x
   evalStateT (update "y" (IntVal 5) >> index "x") initialStore ~?= Nothing
   ]

{- |
We will also need a way to update the values of arrays in the store:
This function takes the name of a variable (that should correspond to
an ArrayVal in the store), and two values i and v (that should both be integers),
and updates the i-th location of the array with the new value v.
-}
     
updateNth :: Name -> Value -> Value -> Eval ()
updateNth n (IntVal i) (IntVal v) = do
   arr <- index n
   case arr of
      ArrayVal elements -> 
         if i < 0 || i >= length elements then 
            lift Nothing
         else 
            let newElements = updateArr elements i v
            in update n $ ArrayVal newElements
      _ -> lift Nothing
updateNth _ _ _ = lift Nothing

updateArr :: [Int] -> Int -> Int -> [Int]
updateArr [] _ _ = []
updateArr (x:xs) i v =
   if i == 0 then v : updateArr xs (i-1) v
   else x : updateArr xs (i-1) v

{- | Expression Evaluator |
   ------------------------

Your next job is to finish `evalE`, an evaluator for expressions.
This function should take as input an expression and return a
store-transformer that yields a `Value`. (See the type of `evalE` below.)

Now implement the rest of `evalE`, referring to the Dafny
to understand what the unary and binary operators should do. You may wish to define
helper functions as part of your implementation. (As a style check, you
should not use `evalStateT`, `execStateT`, or `runStateT` anywhere in
your definition of `evalE` or its helper functions.)

Your expression evaluator should also be *total*.  For any input it should
produce some value. However, we don't have exceptions (or typechecking!), so
if you don't know how to interpret an expression (such as `2 + true` or an
uninitialized variable) your code should return `Nothing`.

-} 


-- | Expression evaluator
evalE :: Expression -> Eval Value
evalE (Val v)       = return v
evalE (Op2 e1 o e2) = do
  v1 <- evalE e1
  v2 <- evalE e2
  lift $ evalOp2 o v1 v2
evalE (Op1 o e) = do
   v <- evalE e
   lift $ evalOp1 o v
evalE (Var (Name n)) = do
   index n
evalE (Var (Proj n e)) = do
   arrVal <- evalE (Var (Name n))
   iVal <- evalE e  
   case (arrVal, iVal) of
      (ArrayVal arr, IntVal i) ->
         if i >= 0 && i < length arr then return $ IntVal $ arr !! i
         else lift Nothing
      _ -> lift Nothing 

evalOp1 :: Uop -> Value -> Maybe Value
evalOp1 Neg (IntVal i) = Just $ IntVal (-i)
evalOp1 Not (BoolVal b) = Just $ BoolVal $ not b
evalOp1 Len (ArrayVal arr) = Just $ IntVal $ length arr
evalOp1 _ _ = Nothing

evalOp2 :: Bop -> Value -> Value -> Maybe Value
evalOp2 Plus (IntVal i1) (IntVal i2) = Just $ IntVal (i1 + i2)
evalOp2 Minus (IntVal i1) (IntVal i2) = Just $ IntVal (i1 - i2)
evalOp2 Times (IntVal i1) (IntVal i2) = Just $ IntVal (i1 * i2)
evalOp2 Divide (IntVal i1) (IntVal i2) = if i2 /= 0 then Just $ IntVal (i1 `div` i2) else Nothing
evalOp2 Modulo (IntVal i1) (IntVal i2) = if i2 /= 0 then Just $ IntVal (i1 `mod` i2) else Nothing
evalOp2 Eq (IntVal i1) (IntVal i2) = Just $ BoolVal (i1 == i2) -- should have for boolean and arrs?
evalOp2 Neq (IntVal i1) (IntVal i2) = Just $ BoolVal (i1 /= i2)
evalOp2 Gt (IntVal i1) (IntVal i2) = Just $ BoolVal (i1 > i2)
evalOp2 Ge (IntVal i1) (IntVal i2) = Just $ BoolVal (i1 >= i2)
evalOp2 Lt (IntVal i1) (IntVal i2) = Just $ BoolVal (i1 < i2)
evalOp2 Le (IntVal i1) (IntVal i2) = Just $ BoolVal (i1 <= i2)
evalOp2 Conj (BoolVal b1) (BoolVal b2) = Just $ BoolVal (b1 && b2)
evalOp2 Disj (BoolVal b1) (BoolVal b2) = Just $ BoolVal (b1 || b2)
evalOp2 Implies (BoolVal b1) (BoolVal b2) = Just $ BoolVal (not b1 || b2)
evalOp2 Iff (BoolVal b1) (BoolVal b2) = Just $ BoolVal (b1 == b2)
evalOp2 _ _ _ = Nothing

-- evalOp2 _ _ _ = undefined


{- |
To test `evalE`, we can write a function that evaluates expressions with a
specified store using the `evalStateT` operation from the `State` monad
library.
-}

evaluate :: Expression -> Store -> Maybe Value
evaluate e = evalStateT (evalE e)

test_evalE :: Test
test_evalE = "evalE tests" ~: TestList [
   -- array indexing
   evaluate (Var (Proj "a" (Val (IntVal 1)))) extendedStore ~?= Just (IntVal 2),
   -- array DNE
   evaluate (Var (Proj "DNE" (Val (IntVal 1)))) extendedStore ~?= Nothing,
   -- array index OOB
   evaluate (Var (Proj "DNE" (Val (IntVal 50)))) extendedStore ~?= Nothing,
   -- Literal Value
   evaluate ((Val (IntVal 42))) Map.empty ~?= Just (IntVal 42),
   -- Testing Negation
   evaluate ((Op1 Neg (Var (Name "x")))) (Map.fromList [("x", IntVal 10)]) ~?= Just (IntVal (-10)),
   -- Testing addition
   evaluate (Op2 (Var (Name "x")) Plus (Var (Name "y"))) (Map.fromList [("x", IntVal 10), ("y", IntVal 20)]) ~?= Just (IntVal 30),
   -- Uninitialized variable
   evaluate (Var (Name "z")) initialStore ~?= Nothing,
   -- Division by 0
   evaluate (Op2 (Var (Name "x")) Divide (Var (Name "y"))) (Map.fromList [("x", IntVal 10), ("y", IntVal 0)]) ~?= Nothing,
   -- addition with a boolean
   evaluate (Op2 (Var (Name "x")) Plus (Var (Name "y"))) (Map.fromList [("x", IntVal 10), ("y", BoolVal True)]) ~?= Nothing
   
   ]

-- testEvalLiteral :: Test
-- testEvalLiteral = TestCase $ do
--     let result = runEval (evalE (Val (IntVal 42))) Map.empty
--     assertEqual "Testing literal integer" (Just (IntVal 42, Map.empty)) result


{- |

Now would be a good time to add more unit test cases for your expression evaluator.
You should also make sure that your expression evaluation *always* returns a result,
even for "buggy" code. Your evaluator should never use "error" or trigger
any sort of runtime exception in Haskell.

(Complete) Statement Evaluator 
------------------------------

In this problem, you will need to implement an evaluator for
statements.  `evalS` should evaluate the given statement
completely, if possible. You may also implement a second evaluator
(`stepS`) that works step-by-step, evaluating only one piece at a time.
Although both evaluators are similar, the first one is a bit simpler. However, this
evaluator could go into an infinite loop if the MiniDafny program does not terminate.
In other words, you should *not* test this evaluator on the program `while true do ; end`.

-}

eval :: Block -> Eval ()
eval (Block ss) = mapM_ evalS ss

-- | Statement evaluator
evalS :: Statement -> Eval ()
evalS (Decl (n, t) e) = do
   v <- evalE e
   update n v 
evalS (Assert (Predicate e)) = do
   result <- evalE e
   case result of
      BoolVal True -> return () 
      BoolVal False -> lift Nothing
      _ -> lift Nothing
evalS (Assign (Name n) e) = do
   -- var <- index n
   v <- evalE e 
   update n v
evalS (Assign (Proj n e1) e2) = do
   arr <- index n
   i <- evalE e1
   v <- evalE e2
   updateNth n i v
evalS (If e b1 b2) = do
   BoolVal v <- evalE e
   if v then eval b1 else eval b2
evalS (While (Predicate p) e b) = do
   BoolVal continue <- evalE e
   when continue $ eval b >> evalS (While (Predicate p) e b)
evalS Empty = return ()

{- |

Don't forget that your evaluator should never call Haskell's "error" or
trigger a runtime exception.

The final step is to implement the evaluator for methods. For that, we simply need to
update an empty store with values for each of its parameters.

-}

runMethod :: Method -> [Value] -> Eval ()
runMethod (Method f ins outs _ ss) vs = do
  guard (length ins == length vs)
  forM_ (zip ins vs) $ \((x,_),v) -> modify $ Map.insert x v
  eval ss

{- | 
  
To test your evaluator, you can use the following function

-}

exec :: Method -> [Value] -> Maybe Store
exec m vs = execStateT (runMethod m vs) initialStore

testM1 = Method "simple" [("x",TInt)] [("result",TInt)] [] (Block [Decl ("x",TInt) (Val (IntVal 10)),Assign (Name "result") (Op2 (Var (Name "x")) Plus (Val (IntVal 5)))])

test_updateNth :: Test
test_updateNth = "updateNth tests" ~: TestList [
   -- If we update the first (0-based) element of "a", then we can find its new value
   evalStateT (updateNth "a" (IntVal 0) (IntVal 42) >> index "a") extendedStore ~?= Just (ArrayVal [42,2,3,4]),
   -- If we try to update a non-array, then we fail
   evalStateT (updateNth "x" (IntVal 0) (IntVal 42)) extendedStore ~?= Nothing,
   -- If we try to update an index out-of-bounds, then we fail
   evalStateT (updateNth "a" (IntVal 5) (IntVal 42)) extendedStore ~?= Nothing
   ]

testEvalE :: Test
testEvalE = "Test Int add & Boolean AND" ~: TestList [
  evaluate (Op2 (Val (IntVal 1)) Plus (Val (IntVal 2))) initialStore ~?= Just (IntVal 3),
  evaluate (Op2 (Val (BoolVal True)) Conj (Val (BoolVal False))) initialStore ~?= Just (BoolVal False)
  ]

testEvalS :: Test
testEvalS = "Test EvalS" ~: TestList [
   execStateT (evalS (Assert (Predicate (Val (BoolVal True))))) Map.empty ~?= Just Map.empty,
   execStateT (evalS (Assert (Predicate (Val (BoolVal False))))) Map.empty ~?= Nothing
  ]


{- |

> -------------------------- Test cases for exec -----------------------------

You can test your evaluator using the sample programs defined in the `Syntax`
module.

However, if you run into bugs, you'll probably want to write some unit tests at this point.

-}

