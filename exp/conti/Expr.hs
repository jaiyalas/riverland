module Expr where
--
import Data.List (find)
import Data.Maybe (fromJust)
import Data.Bifunctor
import Control.Monad.Reader
--
import Debug.Trace
--
type Name = String
--
data Val
    = N Int
    | B Bool
    | Pr Val Val
    | Clos Name Typ Term Typ (DualEnv Val)
    deriving (Show, Eq)
--
data Typ
    = TNat
    | TBool
    | TProd Typ Typ
    | TFun Typ Typ
    deriving (Show, Eq)
--
data Case = (:~>) MTerm Term deriving (Show, Eq)
--
type MTerm = Term
type VTerm = Term
--
data Term
    = Lit Val
    | Var  Name
    | BVar Name
    --
    | Succ Term
    | Pair Term Term
    | Abs Name Typ Term Typ
    | App (Term, Term)
    --
    | LetIn MTerm Term Term
    | RecIn MTerm Term Term
    | BanIn MTerm Term Term
    | DupIn MTerm Term Term
    | AppIn MTerm (Term, Term) Term
    --
    | Match VTerm [Case]
    | MatEq VTerm Case Case
    --
    deriving (Show, Eq)
    --
--
type Compt a = Reader (DualEnv a) a
--
type Cont = Compt Val -> Compt Val
--
eval1 :: Term -> Cont -> Compt Val
eval1 (Lit v) k = k $ return v
eval1 (Var name) k =
    k $ asks (fromJust . peekByKey name . {-traceShowId .-} snd)
eval1 (BVar name) k =
    k $ asks (fromJust . peekByKey name . fst)
eval1 (Succ t) k =
    eval1 t  (>>= \(N n) ->
        k $ return $ N $ (n + 1)
    )
eval1 (Pair t1 t2) k =
    eval1 t1 (>>= \v1 ->
        eval1 t2 (>>= \v2 ->
            k $ return $ Pr v1 v2
        )
    )
eval1 (Abs name tyIn func tyOut) k =
    k $ asks (Clos name tyIn func tyOut)

-- ##
eval1 (App (funT, argT)) k = do
    (Clos pname tyIn fbody tyOut localEnv) <- eval1 funT id
    argv <- eval1 argT id
    k $ local (const $ (pname, argv) `consL` localEnv) (eval1 fbody id)
-- ##
-- eval1 (App (funT, argT)) k = do
--     (Clos pname tyIn fbody tyOut localEnv) <- eval1 funT id
--     argv <- eval1 argT id
--     local (const $ (pname, argv) `consL` localEnv) (eval1 fbody k)
-- ##
-- eval1 (App (funT, argT)) k =
--     eval1 funT (>>= \(Clos pname tyIn fbody tyOut localEnv) ->
--         eval1 argT (>>= \argv ->
--             local (const $ (pname, argv) `consL` localEnv) (eval1 fbody k)
--         )
--     )
--
eval1 (LetIn (Var name) t next) k =
    eval1 t (>>= \v ->
        local (consL (name, v)) (eval1 next k)
    )
eval1 (LetIn (Pair t1 t2) t next) k =
    eval1 t (>>= \(Pr v1 v2) ->
        eval1 (LetIn t1 (Lit v1) $ LetIn t2 (Lit v2) next) k
    )
--
eval1 (RecIn (BVar name) t next) k =
    eval1 t (>>= \(Clos pname tyIn fbody tyOut localEnv) ->
        let funR = Clos pname tyIn fbody tyOut ((name, funR) `consN` localEnv)
        in local (consN (name, funR)) (eval1 next k)
    )
eval1 (BanIn (BVar name) t next) k =
    eval1 t (>>= \v ->
        local (consN (name, v)) (eval1 next k)
    )
eval1 (DupIn (Pair (Var name1) (Var name2)) t next) k =
    eval1 t (>>= \v ->
        eval1 (LetIn (Var name1) (Lit v) $ LetIn (Var name2) (Lit v) next) k
    )
--
eval1 (AppIn var (funT, argT) next) k =
    eval1 (LetIn var (App (funT, argT)) next) k
eval1 (AppIn (Var name) (Abs pname tyIn func tyOut, argT) next) k =
    eval1 argT (>>= \argv ->
        local (consL (pname, argv)) (eval1 func (>>= \resv ->
            local (consL (name, resv)) (eval1 next k))
        )
    )
-- ##
-- eval1 (AppIn (Var name) (funT, argT) next) k = do
--     (Clos pname tyIn fbody tyOut localEnv) <- eval1 funT id
--     argv <- eval1 argT id
--     resv <- local (const $ (pname, argv) `consL` localEnv) (eval1 fbody id)
--     local (consL (name, resv)) (eval1 next k)
-- ## cannot restore env in the last local-invoking
-- eval1 (AppIn (Var name) (funT, argT) next) k =
--     eval1 funT (>>= \(Clos pname tyIn fbody tyOut localEnv) ->
--         eval1 argT (>>= \argv ->
--             local (const $ (pname, argv) `consL` localEnv) (eval1 fbody (>>= \resv ->
--                 local (consL (name, resv)) (eval1 next k))
--             )
--         )
--     )
--
eval1 (Match vt cs) k =
    eval1 vt (>>= \v ->
        let ((nns, nls), next) = fromJust $ findMatched v cs
        in local (bimap (nns +>+) (nls +>+)) (eval1 next k)
    )
eval1 (MatEq vt caseEq caseNEq) k =
    eval1 vt (>>= \(Pr v1 v2) ->
        if v1 == v2
            then eval1 (Match (Lit v1) [caseEq]) k
            else eval1 (Match (Pair (Lit v1) (Lit v2)) [caseNEq]) k
    )
--






--
type DualEnv v =
    ( Env Name v  -- ^ normal
    , Env Name v) -- ^ linear
consL :: (Name, v) -> (DualEnv v) -> (DualEnv v)
consL nv = bimap id ([nv] +>+)
consN :: (Name, v) -> (DualEnv v) -> (DualEnv v)
consN nv = bimap ([nv] +>+) id
--
type Env k v = [(k, v)]
--
(+>+) :: Eq a => Env a b -> Env a b -> Env a b
((k,v):xs) +>+ ys
    | elem k (map fst ys) = (k,v) : xs +>+ (filter ((/= k).fst) ys)
    | otherwise = (k,v) : xs +>+ ys
[] +>+ ys = ys
--
(+<+) :: Eq a => Env a b -> Env a b -> Env a b
((k,v):xs) +<+ ys
    | elem k (map fst ys) = xs +<+ ys
    | otherwise = (k,v) : xs +<+ ys
[] +<+ ys = ys
--
peekByKey :: Eq k => k -> Env k v -> Maybe v
rmByKey   :: Eq k => k -> Env k v -> Env k v
popByKey  :: Eq k => k -> Env k v -> (Maybe v, Env k v)
--
peekByKey k = fmap snd . find ((k==).fst)
rmByKey   k = filter ((k==).fst)
popByKey  k = bimap (peekByKey k) (rmByKey k) . dup
--






matching :: Val -> Term -> Maybe (DualEnv Val)
matching v (Var vname) =
    return $ (vname, v) `consL` mempty
matching v (BVar vname) =
    return $ (vname, v) `consN` mempty
matching (N n1) (Lit (N n2)) = if n1 == n2
    then return mempty
    else Nothing
matching (B b1) (Lit (B b2)) = if b1 == b2
    then return mempty
    else Nothing
matching (N 0) (Succ e) = Nothing
matching (N n1) (Succ e) = matching (N (n1 - 1)) e
matching (Pr v1 v2) (Pair e1 e2) = do
    env1 <- matching v1 e1
    env2 <- matching v2 e2
    return $ env1 `mappend` env2
matching v e = Nothing
--
findMatched :: Val -> [Case] -> Maybe (DualEnv Val, Term)
findMatched v (mat :~> next : cs) =
    maybe (findMatched v cs) (\ctx -> return (ctx, next)) $ matching v mat
findMatched v [] = Nothing







--
run :: Term -> Val
run e = runReader (eval1 e id) ([], [])
--
appRTo :: (Name, Name) -> Name -> Term -> Term
appRTo (f, x) y e = AppIn (Var y) (BVar f, Var x) e
pairVar :: Name -> Name -> Term
pairVar v1 v2 = Pair (Var v1) (Var v2)
dupin :: Term -> Term
dupin e = DupIn (pairVar "a" "b") e (pairVar "a" "b")
--
-- test = succExpr $ plusExpr
--      $ LetIn (Var "x") (Lit $ N 3)
--      $ appRTo ("succ", "x") "y"
--      $ DupIn (Pair (Var "z1") (Var "z2")) (Var "y")
--      $ AppIn (Var "res") (BVar "plus", (Pair (Var "z1") (Var "z2")))
--      $ (Var "res")
--
test = succExpr $ plusExpr
     $ LetIn (Var "x") (Lit $ N 1)
     $ LetIn (Var "y") (Lit $ N 2)
     $ AppIn (Var "z1") (BVar "succ", Var "x")
     $ AppIn (Var "z2") (BVar "succ", Var "y")
     $ AppIn (Var "r") (BVar "plus", Pair (Var "z1") (Var "z2"))
     $ (Var "r")
--
succExpr :: Term -> Term
succExpr next = RecIn (BVar "succ")
    ( Abs "#0" TNat
        (Match (Var "#0")
            [ Lit (N 0) :~> Lit (N 1)
            , Succ (Var "u") :~>
                appRTo ("succ", "u") "u2" (Succ $ Var "u2")
            ])
        TNat -- return type
    ) next
--
plusExpr :: Term -> Term
plusExpr next = RecIn (BVar "plus")
    ( Abs "#0" (TProd TNat TNat)
        ( LetIn (pairVar "_x" "_y") (Var "#0") $
            Match (Var "_y")
            [ Lit (N 0) :~> dupin (Var "_x")
            , Succ (Var "u") :~>
                ( LetIn (Var "#1") (pairVar "_x" "u") $
                    appRTo ("plus", "#1") "z" $
                    LetIn (pairVar "x2" "u2") (Var "z") $
                    Pair (Var "x2") (Succ (Var "u2"))
                )
            ] )
        (TProd TNat TNat) -- return type
    ) next




--
dup :: a -> (a, a)
dup x = (x, x)
