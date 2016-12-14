module RedR where
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

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
evalR :: Env -> Expr -> (Val, Env)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
evalR env (Term vt)
    = appSigma env vt
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
evalR env (LetIn mt (Left vt) e)
    = undefined
evalR env (LetIn mt (Right fapp) e) = undefined
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
evalR env (Match vt []) = undefined
evalR env (Match vt (c : cs)) = undefined
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
evalR env (DupIn mt vt e) = undefined
evalR env (MatEq (Prod vt1 vt2) vase1 case2) = undefined

-- envGen :: ???
