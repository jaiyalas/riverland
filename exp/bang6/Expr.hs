module Expr where
--
import Types
import Ctx
--
type VName   = String
type FunName = String
--
data Nat = Z | S Nat deriving (Eq)
instance Show Nat where show n = "n" ++ show (nat2int n)
--
data Val     = N Nat
             | B Bool
             | Pr Val Val
             | Closure (Ctx VName Val) Expr
             deriving (Eq)
--
type FApp    = (FunName, VTerm)
--
data Case    = (:~>) Expr Expr deriving (Show, Eq)
--
type MTerm = Expr
type VTerm = Expr
--
data Expr = Var VName
          | Lit Val
        --   | Ctr CtrName Expr
          | Suc Expr
          | Pair Expr Expr
          --
          | LamIn MTerm Typ Expr
          | RecIn MTerm Typ Expr Typ
          --
          | AppIn MTerm FApp Expr
          | LetIn MTerm Expr Expr
          | BanIn MTerm Expr Expr
          | DupIn MTerm Expr Expr
          --
          | Match VTerm [Case]
          | MatEq VTerm Case Case
          deriving (Show, Eq)
--
instance Show Val where
    show (N n) = "N" ++ (show $ nat2int n)
    show (B b) = show b
    show (Pr v1 v2) = "("++(show v1)++","++(show v2)++")"
    show (Closure (Ctx xs ys) (LamIn mt ty fbody)) =
        "(C["++(show (mt,ty))++"]"++(show $ length xs)++"/"++(show $ length ys)++")"
--
int2nat :: Int -> Nat
int2nat 0 = Z
int2nat n = S $ int2nat (n-1)
nat2int :: Nat -> Int
nat2int Z = 0
nat2int (S n) = 1 + nat2int n

{-
I'd like to separate Expr and Pattern/Term.
which means I dont want to see any of

    + variable
    + pattern
    + constructor

in the expr-level.

This should be the reason why I use a complicated
variable/pattern definition.

As matter of fact, I hoped to implement this language
in terms of compond calculus mentioned in book "pattern calculus".
However, for the sack of easiness, I should drop this idea
and go back to the traditional way.
-}
