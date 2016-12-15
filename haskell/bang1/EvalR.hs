module EvalR where
--
import Expr
import Func
import Ctx
--

evalRCheck :: Env -> Expr -> Val
evalRCheck env expr =
    let (v, e') = evalR env expr
    in case e' of
        [] -> v
        rest -> error $ "unclean environment: " ++ show rest

-- [("anchor", val)]

mvTrans :: MTerm -> VTerm
mvTrans (Lit v) = Lit v
mvTrans (Atom (Mat ma)) = var ma
mvTrans (Prod mt1 mt2) = Prod (mvTrans mt1) (mvTrans mt2)
mvTrans (NatS mt) = NatS (mvTrans mt)

vmTrans :: VTerm -> MTerm
vmTrans (Lit v) = Lit v
vmTrans (Atom (Var va)) = mat va
vmTrans (Prod vt1 vt2) = Prod (mvTrans vt1) (mvTrans vt2)
vmTrans (NatS vt) = NatS (mvTrans vt)


trans :: (Expr, Expr) -> Expr
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
trans (expr, Term vt) = undefined
trans (expr, Return vt) = undefined
trans (expr, Begin (Match vt (c:cs))) = undefined
trans (expr, Begin (MatEq vt c1 c2)) = undefined
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
trans (expr, LetIn mt (Left vt) e) =
    let mt' = vmTrans vt
        vt' = mvTrans mt
trans (expr, LetIn mt (Right fapp) e) = undefined
trans (expr, Match vt (c : cs)) = undefined
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
trans (expr, DupIn mt vt e) = undefined
trans (expr, MatEq mt case1 case2) = undefined
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
trans (expr, Match vt []) = undefined

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- evalR :: Env -> Expr -> (Val, Env)
-- evalR :: Env -> Expr -> Env
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- evalR env (Term vt) = undefined
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
