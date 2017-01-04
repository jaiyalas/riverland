module Expr where
--
type FName   = String
type FunName = String
--
data Nat = Z | S Nat deriving (Eq)
--
data Val     = N Nat | B Bool | Pair Val Val
             | Closure Expr
             deriving (Show, Eq)
--
data Env = Env Ctx Ctx deriving (Show, Eq)
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
    mempty = Env [] prelude
    mappend (Env xs ys) (Env xs2 ys2) =
        Env (xs +>+ xs2) (ys +>+ ys2)
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
getLiCtx :: Env -> Ctx
getLiCtx (Env x _) = x
getNlCtx :: Env -> Ctx
getNlCtx (Env _ y) = y
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
succExpr :: Expr
succExpr =
    Match (var "#0")
        [ (Lit $ N Z)  :~>
            (Term $ Lit $ N (S Z))
        , (NatS $ mat "u") :~>
            LetIn (mat "u2")
                (Right ("succ", var "u"))
                (Term $ NatS $ var "u2")
        ]
plusExpr :: Expr
plusExpr =
    LetIn (Prod (mat "_x") (mat "_y")) (Left $ var "#0") $
    Match (var "_y")
        [ (Lit (N Z))  :~>
            DupIn (Prod (mat "a") (mat "b")) (var "_x")
                (Term $ Prod (var "a") (var "b"))
        , (NatS $ mat "u") :~>
            LetIn (Prod (mat "x2") (mat "u2"))
                (Right ("plus", Prod (var "_x") (var "u")))
                (Term $ Prod (var "x2") (NatS $ var "u2"))
        ]
plusRExpr :: Expr
plusRExpr =
    MatEq (var "#0")
        ((mat "x")  :~> (Term $ Prod (var "x") (Lit $ N Z)))
        ((Prod (mat "x") (NatS (mat "u"))) :~>
            (LetIn (Prod (mat "x2") (mat "u2"))
                (Right ("plusR", Prod (var "x") (var "u")))
                (Term $ Prod (var "x2") (NatS $ var "u2"))))
negExpr :: Expr
negExpr =
    Match (var "#0")
        [ (Lit (B True))  :~>
            (Term $ Lit $ B False)
        , (Lit (B False)) :~>
            (Term $ Lit $ B True)
        ]
--
prelude :: Ctx
prelude = [ (Var "succ"  , Closure succExpr)
          , (Var "plus"  , Closure plusExpr)
          , (Var "plusR" , Closure plusRExpr)
          , (Var "neg"   , Closure negExpr)
          ]
