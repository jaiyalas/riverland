module Rval where
--
import Data.List (find)
import Data.Maybe (fromJust)
import Data.Bifunctor
import Control.Monad.Reader
--
import Expr
--

-- put 君?
rval0 :: Val -> Term -> Reader (DualEnv Val) (DualEnv Val)
-- --
rval0 v (Lit val)
    | v == val = return mempty
    | otherwise = error $
        "Value " ++ (show v) ++ " ≠ " ++ (show val)
--
rval0 v (Var name)  = asks (consL (name, v))
rval0 v (BVar name) = asks (consN (name, v))
-- -- --
rval0 (N 0) (Succ _) = error "yo"
rval0 (N n) (Succ t) = rval0 (N (n - 1)) t
rval0 (Pr v1 v2) (Pair t1 t2) = do
    env1 <- rval0 v1 t1
    -- local (const env) (rval0 v2 t2)
    env2 <- rval0 v2 t2
    return $ env1 `envUnion` env2

-- --
-- rval0 v
--       (Abs  name2 inTyp2 func2 outTyp2)
rval0 (Clos name1 inTyp1 func1 outTyp1 localEnv)
      (Abs  name2 inTyp2 func2 outTyp2) =
          -- skip everything about checking :(
          return localEnv
--
rval0 v (App (fun, arg)) = do
    env <- ask
    let (Clos name1 _ fbody _ localEnv) = beFun fun env
    returnedEnv <- local (const localEnv) (rval0 v fbody)
    let returnedVal = fromJust $ peekByKey name1 (snd returnedEnv)
    rval0 returnedVal arg

-- -- --
rval0 v (LetIn (Var name) t next) = do
    envNext <- rval0 v next
    let v' = fromJust $ peekByKey name (snd envNext)
    local (const envNext) (rval0 v' t)
-- -- rval0 v (LetIn (Pair t1 t2) t next) = do
rval0 v (LetIn (Pair (Var x) (Var y)) t next) = do
    envNext <- rval0 v next
    let v1 = fromJust $ peekByKey x (snd envNext)
        v2 = fromJust $ peekByKey y (snd envNext)
    local (const envNext) (rval0 (Pr v1 v2) t)
-- this should somehow be implemented via MatEq
rval0 v (DupIn (Pair (Var x) (Var y)) t next) = do
    envNext <- rval0 v next
    let v1 = fromJust $ peekByKey x (snd envNext)
        v2 = fromJust $ peekByKey y (snd envNext)
    if v1 == v2
        then local (const envNext) (rval0 v1 t)
        else error "reversing dupin failed"
rval0 v (BanIn (BVar x) t next) = do
    envNext <- rval0 v next
    let v1 = fromJust $ peekByKey x (fst envNext)
    local (const envNext) (rval0 v1 t)
--
rval0 v (RecIn (BVar name) t next) = do
    envNext <- rval0 v next
    let funClos = fromJust $ peekByKey name (fst envNext)
    local (const envNext) (rval0 funClos t)
-- -- --
rval0 v (Match var cases) = do
    head $ concat $ fmap (oracle v . caseBody) cases
-- rval0 v (MatEq var caseEq caseNEq) = undefined
-- rval0 _ _ = error "yooooo"
--
--
--
-- --
-- oracle :: Val -> Term -> Bool
-- oracle (Pr vl vr) (DupIn mt vt expr)
--     | vl == vr = revMatch (Pr vl vr) (dss expr)
--     | otherwise = False
-- oracle v t = revMatch v (dss expr)

oracle :: Val -> Term -> [Term]
oracle v t =
    fromJust $ sequence $ fmap (ratching v) (dss t)
--
-- -- reversed pattern matching
ratching :: Val -> Term -> Maybe Term
ratching v1 (Lit v2)
    | v1 == v2  = return (Lit v2)
    | otherwise = Nothing
-- -- S n <m> S n
ratching (N n) (Succ vt) =
    ratching (N (n - 1)) vt
-- -- pair
ratching (Pr v1 v2) (Pair vt1 vt2) = do
    r1 <- ratching v1 vt1
    r2 <- ratching v2 vt2
    return (Pair r1 r2)
-- -- irrefusable
ratching _ (Var  v) = return (Var  v)
ratching _ (BVar v) = return (BVar v)
-- -- refusable
ratching _ _ = Nothing
-- -- --
--
--
-- -- headConstructor, aka de-structural-syntax (???????)
-- -- all terms on leaves
dss :: Term -> [Term]
dss (Lit v) = return $ Lit v
dss (Var vt) = return $ Var vt
dss (BVar vt) = return $ BVar vt
dss (Succ t) = fmap Succ (dss t)
dss (Pair e1 e2) = zipWith Pr (dss e1) (dss e2)
-- --
-- dss (Abs _ _ _ _) = error "un-dssable"
dss abs@(Abs _ _ _ _) = return $ abs
-- --
-- e.g.
--     Lit i :~> App f   (Lit j)
--     Var x :~> App f|x (Lit j)
--     Var x :~> App (f, t)
dss (App _)  = error "un-dssable"
-- --
dss (LetIn _ _ next) = dss next
dss (RecIn _ _ next) = dss next
dss (DupIn _ _ next) = dss next
dss (BanIn _ _ next) = dss next
-- -- hmmmmmmm..
dss (Match _ cs) =
    concat $ fmap (dss.caseBody) cs
dss (MatEq t ceq cneq) =
    dss (Match t [ceq, cneq])
-- --
--
-- -- find val by vt; then create val by mt
-- vmGen :: Ctx Var (Val,Typ) -> VTerm -> MTerm -> Ctx Var (Val,Typ)
-- vmGen = \ env vt mt -> vmGenWith env vt mt id
-- --
-- vmGenWith :: Ctx Var (Val,Typ) -> VTerm -> MTerm -> (Val -> Val) -> Ctx Var (Val,Typ)
-- vmGenWith nev vt mt f =
--     insertVal Linear nev mt $ f $ subsVal Linear nev vt
beFun :: Term -> (DualEnv Val) -> Val
beFun (Var  name) = fromJust . peekByKey name . snd
beFun (BVar name) = fromJust . peekByKey name . fst
beFun (Abs pname tyIn fbody tyOut) = Clos pname tyIn fbody tyOut
beFun _ = const (error "not a variable")
