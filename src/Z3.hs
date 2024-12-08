{- | Z3 integration |
   ==================

   The final step in implementing a verifier like Dafny is to
   check whether the verification conditions generated using
   weakest preconditions actually hold. To do that, we will
   use the Z3 theorem prover.

   As discussed in class on Thursday (4/18 -- recording available),
   we will do this by creating a so called "SMTLib" file with the
   extnension .smt2 for _every_ verification condition.

   For an example, consider the first verification condition of our
   "Square.dfy" program: 

     x > 0 && true ==> (0 <= x && 0 == 0 * x)

   This gives rise to the following .smt2 file (available as
   "Square.dfy1.smt2") on the course website.

; Declare Constant x
(declare-const x Int)
(declare-const x Int) <- MINE
; assert the negation of the verification condition:
(assert (not (=> (and (> x 0) true) (and (<= 0 x) (= 0 (* 0 x))))))
(assert (not (=> (and (> x 0) true) (and (<= 0 x) (= 0 (* 0 x)))))) <- MINE
; ask z3 to check it
(check-sat)

    Read below for additional details on the SMT2 format.

    Your task is to create such a file given a Predicate p. We provide
    you with a simple IO handler that relies on a function

      toSMT :: Predicate -> String

    Your final project is to implement this function.  To implement
    this function, we have imported the pretty printing library we
    used in a previous homework. It is highly recommended that you
    mimic the organization of your pretty printers to facilitate
    debugging your code.  That said, you are welcome to use any part
    of the standard library that doesn't require editing the cabal
    file of the project. 

========================
Declaration of Constants 
========================

    The first part of the file is a series of constant declarations with
    the following syntax:

(declare-const <variable-name> <type>)

    Variable names are just strings, and for the purposes of this final
    project, you can assume that all variables that appear in a predicate
    are integers. To lift that assumption we would need to implement a type
    checker for Dafny, which we haven't done.

    Before you begin constructing the .smt2 file, you should calculate
    the variables that appear in a given predicate p, and create a
    declaration such as the one in the example for each one. We have
    imported the Data.Set library for you --- it is recommended that
    you use it, but again, you are welcome to design and implement
    this final project in any way you see fit.
   

==========
Assertions
==========

    The second part of the file is the negation of the verification condition
    where every operation is in prefix form. For example, given the predicate:

      (x > 0 && true) ==> (0 <= x && 0 == 0 * x)

    we will assert it's negation: 

      (assert (not (=> (and (> x 0) true) (and (<= 0 x) (= 0 (* 0 x))))))

    Each operation appears in parentheses before its arguments:
    For example:

           x > 0              translates to              (> x 0)
           0 * x              translates to              (* 0 x)
       false && true          translates to              (and false true)
           0 == x             translates to              (= 0 x)

    While this format makes for syntax that is hard for humans to
    read, you should find that it's much more suitable for being
    automatically generated recursively from the AST of an expression.

=========
Check SAT
=========
   
    As discussed in class, the final part of your file should be a single
    call to check the satisfiability of the assertion you created above:

(check-sat)

    Z3 (and similar solvers) are capable of finding satisfying assignments
    for a plethora of formulas involving integer arithmetic, or returning
    "unsat" if such an assignment doesn't exist. That's why we check for
    the satisfiability of the negation of the verification condition: if
    z3 says that the negation cannot be satisfied, then we are guaranteed
    that it is a tautology that holds in all contexts.

-}
module Z3 where

import Syntax
import Data.List(intersperse)
import Text.PrettyPrint ( (<+>), Doc )
import qualified Text.PrettyPrint as PP

import System.Process(readProcessWithExitCode)
import Data.Set(Set)
import qualified Data.Set as Set

-- | This is the function you need to implement. You can ignore arrays, as with
--   the weakest precondition homework, but everything else needs to be handled!
-- Predicate (Op2 (Op2 (Op2 (Var (Name "x")) Gt (Val (IntVal 0))) Conj (Val (BoolVal True))) Implies (Op2 (Op2 (Val (IntVal 0)) Le (Var (Name "x"))) Conj (Op2 (Val (IntVal 0)) Eq (Op2 (Val (IntVal 0)) Times (Var (Name "x"))))))
-- toSMT :: Predicate -> String
-- toSMT p =
--   let Predicate e = p in
--   let variables = Set.toList $ Set.fromList $ getVariables e in
--   let constants = foldr (\b a -> ("(declare-const " ++ b ++ " Int)\n") ++ a) "" variables in
--   let smtString = toSMTAux e in
--     constants ++ "(assert (not " ++ smtString ++ "))\n(check-sat)"

-- toSMT :: Predicate -> String
-- toSMT (Predicate e) =
--   let variables = getVariables e
--       constants = foldr (\b a -> ("(declare-const " ++ b ++ " Int)\n") ++ a) "" variables
--       smtString = toSMTAux e 
--   in
--     constants ++ "(assert (not " ++ smtString ++ "))\n(check-sat)" "(declare-const a (Array Int Int))\n" 
toSMT :: Predicate -> String
toSMT (Predicate e) =
  let variables = Set.toList $ getVariables e
      constants = foldr (\(n, t) a -> "(declare-const " ++ n ++ " " ++ toSMTType t ++ ")\n" ++ a) "" variables
      smtString = toSMTAux e
      lengthDecl = "(declare-fun length ((Array Int Int)) Int)\n" -- Length function declaration
  in lengthDecl ++ constants ++ "(assert (not " ++ smtString ++ "))\n(check-sat)"

arrayValToSMT :: [Int] -> String
arrayValToSMT arr =
  foldl storeElem "((as const (Array Int Int)) 0)" (zip [0..] arr)
  where
    storeElem acc (i,v) = "(store " ++ acc ++ " " ++ show i ++ " " ++ show v ++ ")"


toSMTAux :: Expression -> String
toSMTAux e = case e of
  Var (Proj n idx)    -> "(select " ++ n ++ " " ++ toSMTAux idx ++ ")"
  Var (Name n)     -> n
  Val (IntVal i)      -> show i
  Val (BoolVal b)     -> if b then "true" else "false"
  Val (ArrayVal arr)  -> arrayValToSMT arr
  Op1 uop expr        -> op1Format uop expr
  Op2 expr1 bop expr2 -> op2Format expr1 bop expr2
  Forall bind expr    -> forallFormat bind expr

  -- let expr = Forall ("x", TInt) (Op2 (Var (Name "x")) Gt (Val (IntVal 0)))
  -- toSMTAux expr --> "(forall ((x Int)) (> x 0))"


-- forallFormat :: Binding -> Expression -> String
-- forallFormat (name, typ) expr =
--   "(forall ((" ++ name ++ " " ++ toSMTType typ ++ ")) " ++ toSMTAux expr ++ ")"
forallFormat :: Binding -> Expression -> String
forallFormat (n, t) expr =
  let smtType = case t of
        TInt -> "Int"
        TBool -> "Bool"
        TArrayInt -> "(Array Int Int)"
  in "(forall ((" ++ n ++ " " ++ smtType ++ ")) " ++ toSMTAux expr ++ ")"


-- Function to convert types to SMT-LIB types.
toSMTType :: Type -> String
toSMTType TInt     = "Int"
toSMTType TBool    = "Bool"
toSMTType TArrayInt = "(Array Int Int)" -- Placeholder for arrays.

op1Format :: Uop -> Expression -> String
op1Format uop expr = case uop of
  Neg -> "(- " ++ toSMTAux expr ++ ")" -- | "-" ++ toSMTAux expr | See if this needs changing (remove parens).
  Not -> "(not " ++ toSMTAux expr ++ ")"
  Len -> "(length " ++ toSMTAux expr ++ ")"

op2Format :: Expression -> Bop -> Expression -> String
op2Format expr1 bop expr2 = 
  "(" ++ opSymbol bop ++ " " ++ toSMTAux expr1 ++ " " ++ toSMTAux expr2 ++ ")"

opSymbol :: Bop -> String
opSymbol Plus    = "+"
opSymbol Minus   = "-"
opSymbol Times   = "*"
opSymbol Divide  = "div"
opSymbol Modulo  = "mod"
opSymbol Eq      = "="
opSymbol Neq     = "distinct"
opSymbol Gt      = ">"
opSymbol Ge      = ">="
opSymbol Lt      = "<"
opSymbol Le      = "<="
opSymbol Conj    = "and"
opSymbol Disj    = "or"
opSymbol Implies = "=>"
opSymbol Iff     = "=" -- see the proper implementation if nec.

-- getVariables :: Expression -> Set.Set String
-- getVariables p = case p of
--   Var (Proj n idx)    -> Set.insert n (getVariables idx)
--   Var (Name n)        -> Set.singleton n
--   Val _               -> Set.empty
--   Op1 uop expr        -> getVariables expr
--   Op2 expr1 bop expr2 -> Set.union (getVariables expr1) (getVariables expr2)
--   Forall bind expr    -> getVariables expr
getVariables :: Expression -> Set (Name, Type)
getVariables e = case e of
  Var (Proj n idx)      -> Set.insert (n, TArrayInt) (getVariables idx) -- Treat as an array
  Var (Name n)          -> Set.singleton (n, TInt)                     -- Scalar variable
  Val _                 -> Set.empty                                   -- No variables in literals
  Op1 _ expr            -> getVariables expr                           -- Recurse on unary operation
  Op2 expr1 _ expr2     -> Set.union (getVariables expr1) (getVariables expr2) -- Combine both sides
  Forall (n, t) expr    -> Set.delete (n, t) (getVariables expr)       -- Exclude bound variables

  -- grab var to be declared


-- | The name of the z3 executable. Change this to whatever it is in your system:
--   In unix based systems, this is just "z3".
--   In Windows, it will be the name of the executable that was installed alongside Dafny.
z3 :: String
z3 = "z3"

-- | This function uses "toSMT" in order to write a file, and invoke z3 on it, checking its
--   output. You're welcome to modify this function as you see fit, the only thing we will
--   automatically test is your "toSMT" function.
convertAndCheck :: Predicate -> String -> IO Bool
convertAndCheck p fn = do
  writeFile fn (toSMT p)
  (_exitCode, stdout, _stderr) <- readProcessWithExitCode z3 [fn] ""
  case stdout of
    's':'a':'t':_ -> return False
    'u':'n':'s':'a':'t':_ -> return True
    _ -> error $ "Z3 output was neither sat or unsat: " ++ stdout
