{- | A Pretty Printer for MiniDafny |
   ==================================

The derived `Show` instances for the datatypes above are pretty hard to
read, especially when programs get long. Really, who wants to read this...

>>> wAbs
> Method "Abs" [("r",TInt)] [("absR",TInt)] [] (Block [If (Op2 (Var (Name "r")) Lt (Val (IntVal 0))) (Block [Assign (Name "absR") (Op1 Neg (Var (Name "r"))),Empty]) (Block [Assign (Name "absR") (Var (Name "r")),Empty])])

instead of this...

    ghci> putStrLn (pretty wAbs)
    method Abs (r : int) returns (absR : int)
    {
        if r < 0 {
            absR := -r;
        }
        else {
            absR := r; 
        }
    }

-}

module Printer where

import Syntax
import Data.List(intersperse)
import Text.PrettyPrint ( (<+>), Doc )
import qualified Text.PrettyPrint as PP

{- |

A *pretty printer* is a function that formats an abstract syntax tree into a
readable representation of the concrete syntax. 

The `pretty` library, imported above as `PP`, provides the following to assist
in the development of pretty printers:

   * An abstract type `Doc` of "pretty documents" that know how to lay
     themselves out prettily. We can use this type to define a class of of types
     that support pretty printing---those that define a function mapping any
     value of that type to a suitable `Doc`.
-} 

class PP a where
  pp :: a -> Doc

{- |

   * Operations for rendering, or converting a `Doc` to text at the
     top level.  The rendering functions are parameterized over display
     options, such as the maximum line length, so that they can figure out
     how to best display the text. 
-}

-- | Default operation for the pretty printer. Displays using standard formatting
-- rules, with generous use of indentation and newlines.
pretty :: PP a => a -> String
pretty = PP.render . pp

-- | Compact version. Displays its argument without newlines.
oneLine :: PP a => a -> String
oneLine = PP.renderStyle (PP.style {PP.mode=PP.OneLineMode}) . pp

{- |
   * Primitive documents and operations for constructing `Doc`s from primitive
     types, such as characters and string.

     For example, we can use the `text` function to define the `Uop` instance of the `PP`
     class.  This instance converts each unary operator into a document.
-}

instance PP Uop where
  pp Neg = PP.char '-'
  pp Not = PP.char '!'
  pp Len = PP.text ".Length"

{- |
   * Combinators for combining `Doc`s in various ways, providing constraints on
     the textual layout. For example, some are listed below. (See the library
     documentation for *many* more.)

          -- An empty document, with no width and no height.
          empty :: Doc

          -- Beside. Combines two documents horizontally with no space between.
          (<>) :: Doc -> Doc -> Doc

          -- Beside, separated by space, unless one of the arguments is `empty`.
          (<+>) :: Doc -> Doc -> Doc

          -- Nest (or indent) a document by a given number of positions
          -- (which may also be negative).
          nest :: Int -> Doc -> Doc

          -- Above. Combines two documents vertically (with overlap if
          -- possible: if the last line of the first argument stops at
          -- least one position before the first line of the second begins,
          -- these two lines are overlapped).
          ($$) :: Doc -> Doc -> Doc

          -- List version of $$.
          vcat :: [Doc] -> Doc

          -- wrap document in (..)
          parens :: Doc -> Doc

          -- wrap document in [..]
          brackets :: Doc -> Doc

          -- wrap document in {..}
          braces :: Doc -> Doc

-}

{- | Pretty-Pretter implementation |
   ---------------------------------

Your job will be to complete the following functionality, ensuring that the output
of the pretty printer is valid Dafny---that is, you can parse it in Visual Studio
if you load it as a .dfy.

-}

-- | We've given you the `PP` instances for String and Int to get started.
instance PP String where
  pp = PP.text

instance PP Int where
  pp = PP.int

-- | TODO: Implement pretty printing for Booleans and lists of integers
instance PP Bool where
  pp True  = PP.text "true"
  pp False = PP.text "false"

instance PP [Int] where
  pp ints = PP.brackets . PP.hcat . PP.punctuate PP.comma $ map pp ints

-- | That should allow you to also pretty pring values if needed.
instance PP Value where
  pp (IntVal i)  = pp i
  pp (BoolVal b) = pp b
  pp (ArrayVal l)  = pp l

-- | TODO: Implement pretty printing for binary operators
instance PP Bop where
  pp Plus    = PP.text "+"
  pp Minus   = PP.text "-"
  pp Times   = PP.text "*"
  pp Divide  = PP.text "/"
  pp Modulo  = PP.text "%"
  pp Eq      = PP.text "=="
  pp Neq     = PP.text "!="
  pp Gt      = PP.text ">"
  pp Ge      = PP.text ">="
  pp Lt      = PP.text "<"
  pp Le      = PP.text "<="
  pp Conj    = PP.text "&&"
  pp Disj    = PP.text "||"
  pp Implies = PP.text "==>"
  pp Iff     = PP.text "<->"

-- | Types and bindings can be pretty printed

instance PP Type where
  pp TInt  = PP.text "int"
  pp TBool = PP.text "bool"
  pp TArrayInt = PP.text "array<int>"

-- | TODO: Implement pretty printing for bindings
instance PP Binding where
  pp (x, t) = PP.text x <+> PP.text ":" <+> pp t

{- |
   Expressions are trickier if you want to avoid putting parentheses everywhere.

   The following code uses two heuristics to ensure minimal parentheses
   are placed:

   * When printing single-operand operations, we don't wrap
     "base" expressions in parentheses.
   * When printing binary operations, we take the precedence level
     of the operator into account.

   We've implemented this logic for you, but there are is one thing
   missing: the array ".Length" operation is now not handled.

-} 

instance PP Expression where
  pp (Var v) = pp v
  pp (Val v) = pp v
  pp (Op1 Len v) = (if isBase v then pp v else PP.parens (pp v)) <> pp Len  
  pp (Op1 o v) = pp o <+> if isBase v then pp v else PP.parens (pp v)
  pp e@Op2{} = ppPrec 0 e  where
     ppPrec n (Op2 e1 bop e2) =
        ppParens (level bop < n) $
           ppPrec (level bop) e1 <+> pp bop <+> ppPrec (level bop + 1) e2
     ppPrec _ e' = pp e'
     ppParens b = if b then PP.parens else id
  -- pp (Forall n e1 e1) = 

isBase :: Expression -> Bool
isBase Val{} = True
isBase Var{} = True
isBase Op1{} = True
isBase _ = False

level :: Bop -> Int
level Times  = 7
level Divide = 7
level Plus   = 5
level Minus  = 5
level Conj   = 1
level Disj   = 1
level Implies = 1
level Iff     = 1
level _      = 2    -- comparison operators

-- | TODO: Implement pretty printing for variables
instance PP Var where
  pp (Name name) = PP.text name
  pp (Proj arrayExpr index) = pp arrayExpr <> PP.brackets (pp index)

-- | TODO: Implement pretty printing for blocks

instance PP Block where
  pp (Block stmts) = PP.vcat [ PP.lbrace, PP.text " " <+> (PP.vcat $ map pp stmts), PP.rbrace ]

-- | TODO: Implement the rest of pretty printing for statements.

instance PP Statement where
  pp Empty = PP.empty
  pp (Decl binding expr) =
    (
      PP.text "var" <+> 
      pp binding <+>
      PP.text ":=" <+> 
      pp expr
    ) <> PP.semi
  -- pp (New binding expr) =
  --   PP.text "var" <+>
  --   pp binding <+>
  --   PP.text ":= new" <+>
  --   pp expr
  pp (Assert predicate) =
    (
      PP.text "assert" <+> 
      pp predicate
    ) <>
    PP.semi
  pp (Assign var expr) =
    (
      pp var <+>
      PP.text ":=" <+>
      pp expr
    ) <> PP.semi
  pp (If expr block1 (Block stmts)) =
    let elseStmt = if null stmts then PP.empty else PP.text "else" <+> (pp (Block stmts))
    in 
    PP.text "if" <+> 
    pp expr 
    <+>
    (pp block1)
    PP.$$
    elseStmt
  pp (While predicates expr block) =
    PP.text "while" <+>
    PP.parens (pp expr)
    PP.$$
    (
      PP.vcat (map (\p -> PP.text "invariant" <+> pp p) [predicates] ++ [pp block])
    )

instance PP [Binding] where
  pp bs = PP.parens $ PP.hsep $ PP.punctuate PP.comma $ map pp bs

-- | TODO: Implement pretty printing for predicates
instance PP Predicate where
  pp (Predicate expr) = pp expr
    -- if null bindings
    --   then PP.empty <+>
    --        pp expr
    -- else PP.text "forall" <+>
    --      PP.hcat (PP.punctuate PP.comma (map pp bindings)) <+>
    --      PP.text "::" <+>
    --      pp expr


-- | TODO: Finally, implement pretty printing for MiniDafny methods

instance PP Specification where
  pp (Requires predicate) = PP.text "requires" <+> pp predicate
  pp (Ensures predicate)  = PP.text "ensures" <+> pp predicate
  pp (Modifies name)      = PP.text "modifies" <+> PP.text name

instance PP Method where
  pp (Method name inputs outputs specs block) =
    let head_var = PP.text "method" <+> pp name <+> 
                PP.parens (PP.hcat $ PP.punctuate PP.comma $ map pp inputs) <+>
                (
                  if not (null outputs) 
                    then PP.text "returns" <+> 
                         PP.parens (PP.hcat $ PP.punctuate PP.comma $ map pp outputs)
                  else PP.empty
                )
        specs' = PP.vcat $ map pp specs
        body = pp block
    in 
      head_var
      PP.$$
      PP.nest 2 specs'
      PP.$$ body

