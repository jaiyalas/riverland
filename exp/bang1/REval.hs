module REval where
--
import Expr
import Ctx
import Func
import Pat
--

-- evalRCheck :: Env -> Expr -> Val
-- evalRCheck env expr =
--     let (v, e') = evalR env expr
--     in case e' of
--         [] -> v
--         rest -> error $ "unclean environment: " ++ show rest

-- [("anchor", val)]


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- evalR (val, env2) exp = env1
-- <==>
-- eval env1 exp = (val, env2)
--
-- eval :: Env -> Expr -> (Val, Env)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
reval :: (Val, Env) -> Expr -> Env
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
reval (v, env) (Term vt) = updateMT env (vmTrans vt) v
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
reval (v, env) (LetIn mt (Left vt) e) =
    let midEnv = reval (v, env) e
        (val, env') = revealVT midEnv (mvTrans mt)
    in updateMT env' (vmTrans vt) val
reval (v, env) (LetIn mt (Right (fname, vt)) e) =
    let midEnv = reval (v, env) e
        (val, env') = revealVT midEnv (mvTrans mt)
        (Closure _ fbody, _) = revealVT prelude (var fname)
        funEnv = reval (val, []) fbody
        (vFunIn, _)= find funEnv (Var "#in")
    in updateMT env' (vmTrans vt) vFunIn
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
reval (v, env) (Match vt []) = error "No pattern can be rev-matched"
reval (v, env) (Match vt (mt :~> cexp : cases)) = if revMatch v (dss cexp)
    then let midEnv = reval (v, env) cexp
             (patVal, finEnv) = revealVT midEnv (mvTrans mt)
         in updateMT finEnv (vmTrans vt) patVal
    else reval (v, env) (Match vt cases)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
reval (v, env) (DupIn mt vt e) =
    undefined
reval (v, env) (MatEq (Prod vt1 vt2) vase1 case2) =
    undefined



--
revMatch :: Val -> VTerm -> Bool
--
revMatch (Closure _ _) _ = False
revMatch _ (Atom _) = True
-- # # # # # # # # # # # # # # # # # #
-- 0 <m> 0
revMatch (N Z) (Lit (N Z)) = True
-- S n <m> S n
revMatch (N (S n)) (Lit (N (S m))) = revMatch (N n) (Lit (N m))
-- 0 <m> S n
revMatch (N Z) (NatS vt) = False
-- S n <m> S n
revMatch (N (S n)) (NatS vt) = revMatch (N n) vt
-- # # # # # # # # # # # # # # # # # #
revMatch (B b) (Lit (B c)) = if b == c then True else False
-- # # # # # # # # # # # # # # # # # #
revMatch (Pair v1 v2) (Prod vt1 vt2) =
    (revMatch v1 vt1) && (revMatch v2 vt2)
-- # # # # # # # # # # # # # # # # # #
revMatch _ _ = False

-- headConstructor, aka de-structural-syntax
dss :: Expr -> VTerm
dss (Term vt) = vt
dss (LetIn mt (Left vt) expr) = dss expr
dss (LetIn mt (Right fapp) expr) = dss expr
dss (DupIn mt vt expr) = dss expr
dss (Match vt cases) = error $ "\"Match\" cannot be DSS-fied"
dss (MatEq vt case1 case2) = error $ "\"MatEq\" cannot be DSS-fied"

-- a case-fliper will be helpful


-- envGen :: ???
