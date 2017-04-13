module Expr where
--
import Types
import Ctx
--
import Data.Maybe (isJust)
import Data.List (find)
import Control.Monad.Reader
--
type FName   = String
type FunName = String
--
data Nat = Z | S Nat deriving (Eq)
--
data Val     = N Nat
            --  | B Bool
             | Pr Val Val
             | Closure (Ctx Var (Val, Typ)) Expr
             deriving (Eq)
--
data Term a = Lit Val
            | Atom a
            | Prod (Term a) (Term a)
            --
            | NatS (Term a)
            | NatZ
            deriving (Show, Eq)
--
newtype Mat     = Mat FName deriving (Show, Eq)
newtype Var     = Var FName deriving (Show, Eq)
type    MTerm   = Term Mat
type    VTerm   = Term Var
--
type FApp    = (FunName, VTerm)
--
data Case    = (:~>) MTerm Expr deriving (Show, Eq)
--
data Expr    = Term VTerm
             | Pair Expr Expr
             | Lambda MTerm Typ Expr
             --
             | AppIn MTerm FApp Expr
             | LetIn MTerm Expr Expr
             | BanIn MTerm Expr Expr
             | DupIn MTerm VTerm Expr
             --
             | Match VTerm [Case]
             | MatEq VTerm Case Case
             deriving (Show, Eq)
--
-- ##### ##### ##### ##### ##### ##### ##### ##### #####
--
int2nat :: Int -> Nat
int2nat 0 = Z
int2nat n = S $ int2nat (n-1)
nat2int :: Nat -> Int
nat2int Z = 0
nat2int (S n) = 1 + nat2int n
--
redN :: Val -> Val
redN (N (S n)) = N n
redN x = error $ "S cannot be destructed from (" ++ (show x) ++ ")"
--
mat :: FName -> MTerm
mat = Atom . Mat
var :: FName -> VTerm
var = Atom . Var
--
mvTrans :: MTerm -> VTerm
mvTrans = fmap (\(Mat x) -> Var x)
--
vmTrans :: VTerm -> MTerm
vmTrans = fmap (\(Var x) -> Mat x)
--
-- ##### ##### ##### ##### ##### ##### ##### ##### #####
--
instance Product Val where
    times = Pr
    piL (Pr x _) = Just x
    piL _ = Nothing
    piR (Pr _ y) = Just y
    piR _ = Nothing
instance Product (Term a) where
    times = Prod
    piL (Prod x _) = Just x
    piL _ = Nothing
    piR (Prod _ y) = Just y
    piR _ = Nothing
instance Product Expr where
    times = Pair
    piL (Pair x _) = Just x
    piL _ = Nothing
    piR (Pair _ y) = Just y
    piR _ = Nothing
-- this should not be Product, Bifunctor maybe
-- instance (Product a, Product b) => Product (a, b) where
--     times (v1, t1) (v2, t2) = (v1 `times` v2, t1 `times` t2)



--
instance Show Nat where
    show n = "n" ++ show (nat2int n)
--
instance Show Val where
    show (N n) = "N" ++ (show $ nat2int n)
    -- show (B b) = show b
    show (Pr v1 v2) = "("++(show v1)++","++(show v2)++")"
    show (Closure (Ctx xs ys) (Lambda mt ty fbody)) =
        "(C["++(show (mt,ty))++"]"++(show $ length xs)++"/"++(show $ length ys)++")"
--
instance Functor Term where
    fmap f (Lit v) = (Lit v)
    fmap f (Atom a) = Atom (f a)
    fmap f (Prod t1 t2) = Prod (fmap f t1) (fmap f t2)
    fmap f (NatS t) = NatS (fmap f t)
    fmap f (NatZ)   = NatZ
