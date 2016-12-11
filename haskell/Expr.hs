module Expr where
--
type FName   = String
type FunName = String
--
data Val     = Pair Val Val
             | N Int
             | B Bool
             deriving (Show, Eq)
--
data Mat     = Mat FName
             deriving (Show, Eq)
data Var     = Var FName
             deriving (Show, Eq)
data Term a  = Lit  Val
             | Atom a
             | Prod  (Term a) (Term a)
             | Fst (Term a)
             | Snd (Term a)
             deriving (Show, Eq)
type MTerm   = Term Mat -- add `Fin i` to make Lit impossible
type VTerm   = Term Var
--
-- function application
type FApp    = (FunName, [VTerm])
data Case    = (:-->) {uncaseMTerm :: MTerm, uncaseExpr :: Expr}
             deriving (Show, Eq)
--
data Expr    = Term VTerm
             | LetIn MTerm (Either VTerm FApp) Expr
             | DupIn MTerm VTerm Expr
             | Match VTerm [Case]
             | MatEq (VTerm, VTerm) Case Case
             deriving (Show, Eq)
--
{-
TODO: add index onto `Term a` for limiting the number of atoms.
TODO: add de brjin index or even locally nameless
-}
