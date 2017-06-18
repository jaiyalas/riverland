module Expr where
--
import Types
import Ctx
--
import Control.Monad
import Data.Either (either)
import Data.Bifunctor
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
type FApp    = (Expr, VTerm)
--
data Case    = (:~>) Expr Expr deriving (Show, Eq)
--
type MTerm = Expr
type VTerm = Expr
--
data Expr = Var VName
          | BVar VName
          | Lit Val
          -- | Ctr CtrName Expr
          | Suc Expr
          | Pair Expr Expr
          | Lam VName Typ Expr Typ {- necessary for recursion -}
          --
          | LetIn MTerm Expr Expr
          | RecIn MTerm Expr Expr
          | AppIn MTerm FApp Expr
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
    show (Closure (Ctx xs ys) (Lam mt tyIn fbody tyOut)) =
        "(C["++(show (mt,tyIn{-,tyOut-}))++"]"++(show $ length xs)++"/"++(show $ length ys)++")"
--
int2nat :: Int -> Nat
int2nat 0 = Z
int2nat n = S $ int2nat (n-1)
nat2int :: Nat -> Int
nat2int Z = 0
nat2int (S n) = 1 + nat2int n
-- well, return both linear and normal free variable names
freeVar :: Expr -> ( [VName]  -- ^ linear
                   , [VName]) -- ^ normal
freeVar (Var  vn) = ([vn], mzero)
freeVar (BVar vn) = (mzero ,[vn])
freeVar (Lit _) = (mzero, mzero)
freeVar (Suc e) = freeVar e
--
freeVar (Pair e1 e2) =
    let (ls1, ns1) = freeVar e1
        (ls2, ns2) = freeVar e2
    in (ls1 `mappend` ls2, ns1 `mappend` ns2)
--
freeVar (Lam vn tyIn fbody tyOut) =
    bimap (filter (/= vn)) (filter (/= vn)) $ freeVar fbody
freeVar (LetIn vn e next) =
    let (ls1, ns1) = freeVar next
        (ls2, ns2) = freeVar e
        (xs, ys) = (freeVar vn)
        foo1 = filter ((flip notElem) xs)
        foo2 = filter ((flip notElem) ys)
    in bimap foo1 foo2 (ls1 `mappend` ls2, ns1 `mappend` ns2)
freeVar (RecIn vn e next) = freeVar (LetIn vn e next)
freeVar (BanIn vn e next) = freeVar (LetIn vn e next)
freeVar (DupIn vn e next) = freeVar (LetIn vn e next)
freeVar (AppIn vn (funE, argE) next) =
    let (ls1, ns1) = freeVar next
        (ls2, ns2) = freeVar argE
        (ls3, ns3) = freeVar funE
        (xs, ys) = (freeVar vn)
        foo1 = filter ((flip notElem) xs)
        foo2 = filter ((flip notElem) ys)
    in bimap foo1 foo2
        ( ls1 `mappend` ls2 `mappend` ls3
        , ns1 `mappend` ns2 `mappend` ns3)
freeVar (Match vn cases) =
    let (ls2, ns2) = freeVar vn
        (ls, ns)   = bimap concat concat $ unzip (map fvCase cases)
    in ( filter ((flip notElem) ls2) ls
       , filter ((flip notElem) ns2) ns )
freeVar (MatEq vn case1 case2) =
    freeVar (Match vn [case1,case2])

fvCase :: Case -> ( [VName]  -- ^ linear
                  , [VName]) -- ^ normal
fvCase (e :~> next) =
    let (xs, ys)   = freeVar e
        (ls1, ns1) = freeVar next
    in ( filter ((flip notElem) xs) ls1
       , filter ((flip notElem) ys) ns1 )
