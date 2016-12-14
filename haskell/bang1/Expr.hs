module Expr where
--
type FName   = String
type FunName = String
--
data Nat = Z | S Nat deriving (Show, Eq)

int2nat :: Int -> Nat
int2nat 0 = Z
int2nat n = S $ int2nat (n-1)
nat2int :: Nat -> Int
nat2int Z = 0
nat2int (S n) = 1 + nat2int n
--
data Val     = Pair Val Val
             | N Nat
             | B Bool
             deriving (Show, Eq)
--
redN :: Val -> Val
redN (N (S n)) = N n
redN _ = error "Destruction on Nat is failed"

--
data Mat     = Mat FName
             deriving (Show, Eq)
data Var     = Var FName
             deriving (Show, Eq)
--
data Term a  = Lit Val
             | Atom a
             | Prod (Term a) (Term a)
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
-- call-by-name function application
type FApp    = (FunName, [VTerm])
--
data Case    = (:~>) { uncasePatt :: MTerm
                     , uncaseExpr :: Expr}
             deriving (Show, Eq)
--
data Expr    = Term VTerm
             | Return VTerm
             | LetIn MTerm (Either VTerm FApp) Expr
             | DupIn MTerm VTerm Expr
             | Match VTerm [Case]
             | MatEq VTerm Case Case
             deriving (Show, Eq)
--
