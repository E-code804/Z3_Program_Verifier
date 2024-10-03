{- | A Parser for MiniDafny
     ======================
-} 

module DafnyParser where

import Control.Applicative
import qualified Data.Char as Char
import Syntax
import Printer
import Parser (Parser)
import qualified Parser as P
import Test.HUnit  (runTestTT,Test(..),Assertion, (~?=), (~:), assert, Counts)

{- | Tests the Parser
      ------------------
-}

prop_roundtrip_val :: Value -> Bool
prop_roundtrip_val v = P.parse valueP (pretty v) == Right v

prop_roundtrip_exp :: Expression -> Bool
prop_roundtrip_exp e = P.parse expP (pretty e) == Right e

prop_roundtrip_stat :: Statement -> Bool
prop_roundtrip_stat s = P.parse statementP (pretty s) == Right s

{- | More Parser combinators
     -----------------------

Helper functions that we can use later.

In general, so that our parsers are flexible about spaces that appear in
source programs, all of the parsers will need to skip over any trailing white
space.

-}

wsP :: Parser a -> Parser a
wsP p = p <* many P.space

test_wsP :: Test
test_wsP = TestList [
  P.parse (wsP P.alpha) "a" ~?= Right 'a',
  P.parse (many (wsP P.alpha)) "a b \n   \t c" ~?= Right "abc"
  ]

{- |
Use this to define a parser that accepts *only* a particular string `s`
and consumes any white space that follows. The last test case ensures
that trailing whitespace is being treated appropriately.
-}

stringP :: String -> Parser ()
stringP s = wsP $ P.string s *> pure ()

test_stringP :: Test
test_stringP = TestList [
  P.parse (stringP "a") "a" ~?= Right (),
  P.parse (stringP "a") "b" ~?= Left "No parses",
  P.parse (many (stringP "a")) "a  a" ~?= Right [(),()]
  ]

-- | Define a parser that will accept a particular string `s`, returning a
-- | given value `x`, and also and consume any white space that follows.

constP :: String -> a -> Parser a
constP s a = wsP $ stringP s *> pure a

test_constP :: Test
test_constP = TestList [
  P.parse (constP "&" 'a')  "&  " ~?=  Right 'a',
  P.parse (many (constP "&" 'a'))  "&   &" ~?=  Right "aa"
  ]

-- | We will also use `stringP` for some useful operations that parse between
-- | delimiters, consuming additional whitespace.

parens :: Parser a -> Parser a
parens x = P.between (stringP "(") x (stringP ")")

braces :: Parser a -> Parser a
braces x = P.between (stringP "{") x (stringP "}")

-- >>> P.parse (many (brackets (constP "1" 1))) "[1] [  1]   [1 ]"
-- Right [1,1,1]
brackets :: Parser a -> Parser a
brackets x = P.between (stringP "[") x (stringP "]")



{- | Parsing Constants -}

valueP :: Parser Value
valueP = intValP <|> boolValP

-- >>> P.parse (many intValP) "1 2\n 3"
-- Right [IntVal 1,IntVal 2,IntVal 3]
intValP :: Parser Value
intValP = wsP $ IntVal <$> P.int

-- >>> P.parse (many boolValP) "true false\n true"
-- Right [BoolVal True,BoolVal False,BoolVal True]
boolValP :: Parser Value
boolValP = wsP $ trueP <|> falseP where
  trueP, falseP :: Parser Value
  trueP  = pure (BoolVal True) <* P.string "true"
  falseP = pure (BoolVal False) <* P.string "false"

-- | At this point, tests using the `prop_roundtrip_val` should work. 

{- | Parsing Types -}

typeP :: Parser Type
typeP = constP "int" TInt <|> constP "bool" TBool <|> constP "array<int>" TArrayInt

{- | Parsing Expressions -} 

expP :: Parser Expression -- something wrong here when trying: P.parse specificationP "ensures isPrime <==> (m > 1 && forall j : int :: 2 <= j < m ==> m % j != 0)"
expP    = conjP where
  conjP   = compP `P.chainl1` opAtLevel (level Conj)  
  compP   = catP `P.chainl1` opAtLevel (level Gt)
  catP    = sumP `P.chainl1` opAtLevel (level Eq)
  sumP    = prodP `P.chainl1` opAtLevel (level Plus)
  prodP   = uopexpP `P.chainl1` opAtLevel (level Times)
  uopexpP = baseP
      <|> Op1 <$> uopP <*> uopexpP 
  baseP = lenP
       <|> Var <$> varP
       <|> parens expP
       <|> Val <$> valueP
      -- .Length here

-- | Parse an operator at a specified precedence level
opAtLevel :: Int -> Parser (Expression -> Expression -> Expression)
opAtLevel l = flip Op2 <$> P.filter (\x -> level x == l) bopP

-- >>>  P.parse (many varP) "x y z"
-- Right [Name "x", Name "y", Name "z"]
-- >>> P.parse varP "y[1]"
-- Right (Proj "y" (Val (IntVal 1)))
varP :: Parser Var
varP = (Proj <$> nameP <*> brackets expP) <|> (Name <$> nameP)

lenP :: Parser Expression
lenP = (Op1 Len . Var . Name) <$> (nameP <* stringP ".Length")

{- | 
Define an expression parser for names. Names can be any sequence of upper and
lowercase letters, digits and underscores, not beginning with a digit and not
being a reserved word. Your parser should also consume any trailing
whitespace characters.
-}

reserved :: [String]
reserved = [ "assert", "break","else","Length"
 ,"false","for","function","invariant","if","in"
 ,"return","true","method","int", "bool"
 ,"while", "requires","ensures"]

-- >>> P.parse (many nameP) "x sfds _ int"
-- Right ["x","sfds", "_"]
nameP :: Parser Name
nameP = wsP $ P.filter (not . (`elem` reserved)) ( (:) <$> firstChar <*> many nextChars ) where
  firstChar, nextChars :: Parser Char
  firstChar = P.satisfy (\c -> Char.isAlpha c || c == '_') -- check if _ can be first
  nextChars = P.alpha <|> P.digit <|> P.char '_'

-- Now write parsers for the unary and binary operators. Make sure you
--  check out the Syntax module for the list of all possible
--  operators. The tests are not exhaustive.

-- >>> P.parse (many uopP) "- - !"
-- Right [Neg,Neg,Not]
uopP :: Parser Uop
uopP = wsP $ negP <|> notP where
  negP, notP :: Parser Uop
  negP = constP "-" Neg
  notP = constP "!" Not

-- >>> P.parse (many bopP) "+ >= &&"
-- Right [Plus,Ge,Conj]
bopP :: Parser Bop
bopP = wsP $ iffP <|> impP <|> plusP <|> minusP <|> timesP <|> divP <|> modP <|> eqP <|> neqP <|> geP <|> leP <|> gtP <|> ltP <|> conjP <|> disjP where
  plusP, minusP, timesP, divP, modP, eqP, neqP, geP, gtP, leP, ltP, conjP, disjP, impP, iffP :: Parser Bop
  plusP  = constP "+" Plus
  minusP = constP "-" Minus
  timesP = constP "*" Times
  divP   = constP "/" Divide
  modP   = constP "%" Modulo
  eqP    = constP "==" Eq
  neqP   = constP "!=" Neq
  geP    = constP ">=" Ge
  gtP    = constP ">" Gt
  leP    = constP "<=" Le
  ltP    = constP "<" Lt
  conjP  = constP "&&" Conj
  disjP  = constP "||" Disj
  impP   = constP "==>" Implies
  iffP   = constP "<==>" Iff

-- | At this point you should be able to test the  `prop_roundtrip_exp` property.

{- | Parsing Statements
     ------------------

First, define a parser for bindings... 

-}

bindingP :: Parser Binding
bindingP = wsP $ (,) <$> nameP <* stringP ":" <*> typeP

singleBindP, multiBindP :: Parser [Binding]
singleBindP = wsP $ many bindingP
multiBindP  = wsP $ bindingP `P.sepBy` (stringP ",")

forAllSingleBindP :: Parser Binding
forAllSingleBindP = wsP $ bindingP

-- | ...and predicates...
predicateP :: Parser Predicate
predicateP = wsP $ forAllP <|> justExprP where
  justExprP, forAllP :: Parser Predicate
  justExprP = liftA Predicate expP
  forAllP   = Predicate <$> (Forall <$> (stringP "forall" *> forAllSingleBindP <* stringP "::") <*> expP)
     -- Works for: P.parse predicateP "forall x : int :: x > 0"
     -- Does not work for P.parse predicateP "forall x :: x > 0"

-- | Finally, define a parser for statements:

optionalParensExpP :: Parser Expression
optionalParensExpP = wsP $ expP <|> parens expP

emptyPredicate :: Predicate
emptyPredicate = Predicate (Val (BoolVal True))

statementP :: Parser Statement
statementP = wsP $ declP <|> assertP <|> assignP <|> ifP <|> emptyP <|> whileP where
  declP, assertP, assignP, ifP, whileP :: Parser Statement
  declP   = Decl <$> (stringP "var" *> bindingP <* stringP ":=") <*> expP
  assertP = Assert <$> (stringP "assert" *> predicateP)
  assignP = Assign <$> varP <* stringP ":=" <*> expP
  ifP     = If <$> (stringP "if" *> expP) <*> braces blockP <*> ((stringP "else" *> braces blockP) <|> pure (Block []))
  emptyP  = pure Empty <* stringP ";"
  whileP  = noPredP <|> withPredP where
     noPredP, withPredP :: Parser Statement
     noPredP   = (flip While <$> (stringP "while" *> optionalParensExpP) <*> pure emptyPredicate) <*> braces blockP
     withPredP = (flip While <$> (stringP "while" *> optionalParensExpP) 
                 <*> (stringP "invariant" *> predicateP)) -- may need many here for multiple invariants
                 <*> braces blockP


invariantP :: Parser Predicate
invariantP = (stringP "invariant" *> predicateP) <|> pure (Predicate (Val (BoolVal True)))

-- | ... and one for blocks.

blockP :: Parser Block
blockP = wsP $ Block <$> many statementP

{- | Parsing Methods
     ---------------

   Implement parsing for methods. You will probably want to modularize it
   by implementing parsing for specifications and many bindings.

-}

specificationP :: Parser Specification
specificationP = wsP $ requiresP <|> ensuresP <|> modifiesP where
     requiresP, ensuresP, modifiesP :: Parser Specification
     requiresP = Requires <$> (stringP "requires" *> predicateP)
     ensuresP  = Ensures <$> (stringP "ensures" *> predicateP)
     modifiesP = Modifies <$> (stringP "modifies" *> nameP)

methodP :: Parser Method -- make sure wsP is consumed, cases w/ no specification
methodP = wsP $ Method <$> (stringP "method" *> nameP) 
               <*> paramsP
               <*> returnsP
               <*> specificationsP
               <*> braces blockP 
          where 
          paramsP, returnsP :: Parser [Binding]
          paramsP  = parens (multiBindP <|> singleBindP <|> pure [])
          returnsP = (stringP "returns" *> paramsP) <|> pure []
          
          specificationsP :: Parser [Specification]
          specificationsP = many specificationP <|> pure []

 
{- | Parsing Expressions and Files
     -----------------------------

Finally, we'll export these convenience functions for calling
the parser.

-}

parseDafnyExp :: String -> Either P.ParseError Expression
parseDafnyExp = P.parse expP 

parseDafnyStat :: String -> Either P.ParseError Statement
parseDafnyStat = P.parse statementP

parseDafnyFile :: String -> IO (Either P.ParseError Method)
parseDafnyFile = P.parseFromFile (const <$> methodP <*> P.eof) 

{- File-based tests
   ----------------
-}

--tParseFiles :: Test
--tParseFiles = "parse files" ~: TestList [
--                 "abs"  ~: p "dafny/abs.dfy"  wAbs,
--                 "minVal"  ~: p "dafny/findMinVal.dfy"  wMinVal,
--                 "minIndex"  ~: p "dafny/findMinIndex.dfy"  wMinIndex,                 
--                 "minMax"   ~: p "dafny/minMax.dfy"   wMinMax,
--                 "arraySpec" ~: p "dafny/arraySpec.dfy" wArraySpec
--               ] where
--   p fn ast = do
--     result <- parseDafnyFile fn
--     case result of
--       (Left _) -> assert False
--       (Right ast') -> assert (ast == ast')

{- | Unit Tests
      ---------

These unit tests summarize the tests given above.
-}

test_comb = "parsing combinators" ~: TestList [
 P.parse (wsP P.alpha) "a" ~?= Right 'a',
 P.parse (many (wsP P.alpha)) "a b \n   \t c" ~?= Right "abc",
 P.parse (stringP "a") "a" ~?= Right (),
 P.parse (stringP "a") "b" ~?= Left "No parses",
 P.parse (many (stringP "a")) "a  a" ~?= Right [(),()],
 P.parse (constP "&" 'a')  "&  " ~?=  Right 'a',
 P.parse (many (constP "&" 'a'))  "&   &" ~?=  Right "aa",
 P.parse (many (brackets (constP "1" 1))) "[1] [  1]   [1 ]" ~?= Right [1,1,1]
 ]

test_value = "parsing values" ~: TestList [
 P.parse (many intValP) "1 2\n 3" ~?= Right [IntVal 1,IntVal 2,IntVal 3],
 P.parse (many boolValP) "true false\n true" ~?= Right [BoolVal True,BoolVal False,BoolVal True]
 ]

test_exp = "parsing expressions" ~: TestList [
 P.parse (many varP) "x y z" ~?= Right [Name "x", Name "y", Name "z"],
 P.parse (many nameP) "x sfds _" ~?= Right ["x","sfds", "_"],
 P.parse (many uopP) "- -" ~?=  Right [Neg,Neg],
 P.parse (many bopP) "+ >= .." ~?= Right [Plus,Ge]
 ]

test_stat = "parsing statements" ~: TestList [
 P.parse statementP ";" ~?= Right Empty,
 P.parse statementP "x := 3" ~?= Right (Assign (Name "x") (Val (IntVal 3))),
 P.parse statementP "if x { y := true; }" ~?=
    Right (If (Var (Name "x")) (Block [Assign (Name "y") (Val $ BoolVal True), Empty]) (Block [])),
 P.parse statementP "while 0 { }" ~?=
    Right (While (Predicate (Val (BoolVal True))) (Val (IntVal 0)) (Block []))
   ]

-- | Testing summary
--------------------

test_all :: IO Counts
test_all = runTestTT $ TestList [ test_comb, test_value, test_exp, test_stat] --, tParseFiles ]

