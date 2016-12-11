module Expr where
--
type FName   = String
type FunName = String
--
data Nat = Z | S {unS :: Nat} deriving (Show, Eq)
--
data Val     = Pair Val Val
             | N {unN :: Nat}
             | B Bool
             deriving (Show, Eq)
--
redN :: Val -> Val
redN = N . unS . unN
--
data Mat     = Mat FName
             deriving (Show, Eq)
data Var     = Var FName
             deriving (Show, Eq)
--
data Term a  = Lit Val
             | Atom a
             | Prod (Term a) (Term a)
             | Fst  (Term a)
             | Snd  (Term a)
             --
             | NatS (Term a)
             deriving (Show, Eq)
--
type MTerm   = Term Mat -- add `Fin i` to make Lit impossible
type VTerm   = Term Var
--
mat :: FName -> MTerm
mat = Atom . Mat
var :: FName -> VTerm
var = Atom . Var
--
-- call-by-named function application
type FApp    = (FunName, [VTerm])
data Case    = (:-->) {uncasePatt :: MTerm, uncaseExpr :: Expr}
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
