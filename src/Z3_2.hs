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
; assert the negation of the verification condition:
(assert (not (=> (and (> x 0) true) (and (<= 0 x) (= 0 (* 0 x))))))
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
module Z3_2 where

import Syntax
import Data.List(intersperse)
import Text.PrettyPrint ( (<+>), Doc )
import qualified Text.PrettyPrint as PP

import System.Process(readProcessWithExitCode)
import Data.Set(Set)
import qualified Data.Set as Set

-- | This is the function you need to implement. You can ignore arrays, as with
--   the weakest precondition homework, but everything else needs to be handled!

toSMT :: Predicate -> String
toSMT (Predicate e) = 
    let vars = extractVariables e
        declarations = declareVariables vars
        negation = assertNegation (Predicate e)
    in declarations ++ negation ++ "\n(check-sat)"

declareVariables :: Set Name -> String
declareVariables vars = unlines $ map (\v -> "(declare-const " ++ v ++ " Int)") (Set.toList vars)

assertNegation :: Predicate -> String
assertNegation (Predicate e) = "(assert (not " ++ translateExpression e ++ "))"

extractVariables :: Expression -> Set Name
extractVariables expr = case expr of
    Var v -> case v of
        Name n -> Set.singleton n
        Proj n _ -> Set.singleton n
    Val _ -> Set.empty
    Op1 _ e -> extractVariables e
    Op2 e1 _ e2 -> Set.union (extractVariables e1) (extractVariables e2)

translateExpression :: Expression -> String
translateExpression expr = case expr of
    Var v -> translateVar v
    Val v -> translateValue v
    Op1 op e -> translateUnaryOp op e
    Op2 e1 op e2 -> translateBinaryOp e1 op e2

translateVar :: Var -> String
translateVar (Name n) = n
translateVar (Proj n e) = error "Ignore"

translateValue :: Value -> String
translateValue (IntVal i) = show i
translateValue (BoolVal b) = if b then "true" else "false"
translateValue _ = error "Ignore"

translateUnaryOp :: Uop -> Expression -> String
translateUnaryOp Neg e = "(- " ++ translateExpression e ++ ")"
translateUnaryOp Not e = "(not " ++ translateExpression e ++ ")"
translateUnaryOp Len e = error "Ignore"

translateBinaryOp :: Expression -> Bop -> Expression -> String
translateBinaryOp e1 op e2 =
    "(" ++ opToSmt op ++ " " ++ translateExpression e1 ++ " " ++ translateExpression e2 ++ ")"

opToSmt :: Bop -> String
opToSmt Plus = "+"
opToSmt Minus = "-"
opToSmt Times = "*"
opToSmt Divide = "div"
opToSmt Modulo = "mod"
opToSmt Eq = "="
opToSmt Neq = "distinct"
opToSmt Gt = ">"
opToSmt Ge = ">="
opToSmt Lt = "<"
opToSmt Le = "<="
opToSmt Conj = "and"
opToSmt Disj = "or"
opToSmt Implies = "=>"
opToSmt Iff = "="

translatePredicate :: Predicate -> String
translatePredicate (Predicate e) = translateExpression e

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
