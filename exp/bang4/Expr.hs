module Expr where
--
type FName   = String
type FunName = String
--
data Nat = Z | S Nat deriving (Eq)
--
data Val     = N Nat
             | B Bool
             | Pr Val Val
             | Closure Env Expr
             deriving (Show, Eq)
--
data Term a  = Lit Val
             | Atom a
             | Prod (Term a) (Term a)
             | NatS (Term a)
             deriving (Show, Eq)
--
instance Functor Term where
    fmap f (Lit v) = (Lit v)
    fmap f (Atom a) = Atom (f a)
    fmap f (Prod t1 t2) = Prod (fmap f t1) (fmap f t2)
    fmap f (NatS t) = NatS (fmap f t)
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
             | Lambda MTerm Expr {-Atomic mt-}
             --
             | LetIn MTerm (Either Expr FApp) Expr
             | DupIn MTerm VTerm Expr
             | Pair Expr Expr
             --
             | Match VTerm [Case]
             | MatEq VTerm Case Case
             deriving (Show, Eq)
--
type Ctx = [(Var, Val)]
--
data Env = Env Ctx Ctx deriving (Show, Eq)
--
instance Monoid Env where
    mempty = Env [] []
    mappend (Env xs ys) (Env xs2 ys2) =
        Env (xs +>+ xs2) (ys +>+ ys2)
--
data CtxSwitch = Normal | Linear deriving (Show, Eq)
--
-- ##### ##### ##### ##### ##### ##### ##### ##### #####
--
(+>+) :: Eq a => [(a,b)] -> [(a,b)] -> [(a,b)]
((k,v):xs) +>+ ys
    | elem k (map fst ys) = (k,v) : xs +>+ (filter ((/= k).fst) ys)
    | otherwise = (k,v) : xs +>+ ys
[] +>+ ys = ys

(+<+) :: Eq a => [(a,b)] -> [(a,b)] -> [(a,b)]
((k,v):xs) +<+ ys
    | elem k (map fst ys) = xs +<+ ys
    | otherwise = (k,v) : xs +<+ ys
[] +<+ ys = ys
--
getLCtx :: Env -> Ctx
getLCtx (Env x _) = x
getNCtx :: Env -> Ctx
getNCtx (Env _ y) = y
--
headL :: Env -> Maybe (Var, Val)
headL (Env (x : xs) _) = Just x
headL (Env [] _) = Nothing
headN :: Env -> Maybe (Var, Val)
headN (Env _ (y : ys)) = Just y
headN (Env _ []) = Nothing
--
consL :: (Var, Val) -> Env -> Env
consL vv (Env lis nls) = (Env (vv : lis) nls)
consN :: (Var, Val) -> Env  -> Env
consN vv (Env lis nls) = (Env lis (vv : nls))
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
