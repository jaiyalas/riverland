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
reval (v, env) (Match vt []) =
    undefined
reval (v, env) (Match vt (c : cs)) =
    undefined
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
reval (v, env) (DupIn mt vt e) =
    undefined
reval (v, env) (MatEq (Prod vt1 vt2) vase1 case2) =
    undefined

-- envGen :: ???
