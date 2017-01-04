module Expr where
--
type FName   = String
type FunName = String
--
data Nat = Z | S Nat deriving (Eq)
--
data Val     = N Nat | B Bool | Pair Val Val
             | Closure Env Expr
             deriving (Show, Eq)
--
data Env = Env Ctx Ctx
type Ctx = [(Var, Val)]
--
data Term a  = Lit Val
             | Atom a
             | Prod (Term a) (Term a)
             | NatS (Term a)
             deriving (Show, Eq)
--
newtype Mat     = Mat FName deriving (Show, Eq)
type    MTerm   = Term Mat
newtype Var     = Var FName deriving (Show, Eq)
type    VTerm   = Term Var
--
type FApp    = (FunName, VTerm)
--
data Case    = (:~>) MTerm Expr deriving (Show, Eq)
--
data Expr    = Term VTerm
             --
             | LetIn MTerm (Either VTerm FApp) Expr
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
instance Show Nat where
    show n = "n" ++ show (nat2int n)
--
redN :: Val -> Val
redN (N (S n)) = N n
redN _ = error "Destruction on Nat is failed"
--
mat :: FName -> MTerm
mat = Atom . Mat
var :: FName -> VTerm
var = Atom . Var
--
mvTrans :: MTerm -> VTerm
mvTrans (Lit v) = Lit v
mvTrans (Atom (Mat ma)) = var ma
mvTrans (Prod mt1 mt2) = Prod (mvTrans mt1) (mvTrans mt2)
mvTrans (NatS mt) = NatS (mvTrans mt)
--
vmTrans :: VTerm -> MTerm
vmTrans (Lit v) = Lit v
vmTrans (Atom (Var va)) = mat va
vmTrans (Prod vt1 vt2) = Prod (vmTrans vt1) (vmTrans vt2)
vmTrans (NatS vt) = NatS (vmTrans vt)
--
instance Monoid Env where
    mempty = Env [] []
    mappend (Env xs ys) (Env xs2 ys2) =
        Env (xs ++ xs2) (ys ++ ys2)
--
getLiCtx :: Env -> Ctx
getLiCtx (Env x _) = x
getNlCtx :: Env -> Ctx
getNlCtx (Env _ y) = y
--
headLi :: Env -> Maybe (Var, Val)
headLi (Env (x : xs) _) = Just x
headLi (Env [] _) = Nothing
headNl :: Env -> (Var, Val)
headNl (Env _ (y : ys)) = Just y
headNl (Env _ []) = Nothing
--
putLiCtx :: Env -> (Var, Val) -> Env
putLiCtx (Env lis nls) vv = (Env (vv : lis) nls)
putNlCtx :: Env -> (Var, Val) -> Env
putNlCtx (Env lis nls) vv = (Env lis (vv : nls))
--
