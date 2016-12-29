module REval where
--
import Expr
import Ctx
import Func
import Pat
--

evalRCheck :: Env -> Expr -> Val
evalRCheck env expr =
    let (v, e') = evalR env expr
    in case e' of
        [] -> v
        rest -> error $ "unclean environment: " ++ show rest

-- [("anchor", val)]


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

evalR (val, env2) exp = env1
<==>
eval env1 exp = (val, env2)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
reval :: Env -> Expr -> (Val, Env)
-- evalR :: Env -> Expr -> Env
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
reval env (Term vt) = revealVT env vt
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- whenever Return is reached, there must have exactly one variable in env
-- -- followed by the setting in Func, this variable should have name as "#0"
-- evalR env (Return vt) =
--     let (v, env') = appSigma env (var "#0")
--         mt = vmTrans vt
--     in zipMatEnv v mt  env'
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- evalR env (LetIn mt (Left vt) e) =
--     let vt' = mvTrans mt
--         mt' = vmTrans vt
-- evalR env (LetIn mt (Right fapp) e) =
--     undefined
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- evalR env (Match vt []) =
--     undefined
-- evalR env (Match vt (c : cs)) =
--     undefined
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- evalR env (DupIn mt vt e) =
--     undefined
-- evalR env (MatEq (Prod vt1 vt2) vase1 case2) =
--     undefined

-- envGen :: ???
