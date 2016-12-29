module Eval where
--
import Expr
import Func
import Ctx
import Pat
--
--
eval :: Env -> Expr -> (Val, Env)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
eval env (Term vt)    = revealVT env vt
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
eval env (LetIn mt (Left vt) e) =
    let (val, env') = revealVT env vt
        newEnv = updateMT env' mt val
    in eval newEnv e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
eval env (LetIn mt (Right (fun, vt)) e) =
    let (Closure _ fbody, _) = revealVT prelude (var fun)
        (val, env') = revealVT env vt
        (res, _) = eval [(Var "#in", val)] fbody
        newEnv = updateMT env' mt res
    in eval newEnv e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
eval env (DupIn (Prod (Atom (Mat ma1)) (Atom (Mat ma2))) (Atom va) e) =
        let (val, env') = find env va
            newEnv = (Var ma2, val) : (Var ma1, val) : env'
        in eval newEnv e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
eval env (Match vt cases) =
    let (val, env1) = revealVT env vt
        (env2, e) = matching val cases
    in eval (env1 ++ env2) e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
eval env (MatEq vt case1 case2) = case revealVT env vt of
    ((Pair val1 val2), env2) ->
        if val1 == val2
            then case case1 of
                (Atom (Mat ma) :~> e1) ->
                    eval ((Var ma, val2) : env2) e1
                (NatS (Atom (Mat ma)) :~> e2) ->
                    eval ((Var ma, redN val1) : env2) e2
                _ -> error "matching failed in MatEq (case1)"
            else case case2 of
                (Prod mt1 mt2 :~> e1) ->
                    let newEnv = updateMT (updateMT env2 mt1 val1) mt2 val2
                    in eval newEnv e1
                _ -> error "matching failed in MatEq (case2)"
    otherwise -> error $ "mateq failed with " ++ show vt
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --
eval _ _ = error "failure in matching with eval"
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --

--

test_neg :: (Val, Env)
test_neg = eval [(Var "#in", B False)] negExpr

test_plus :: (Int, Int) -> (Val, Env)
test_plus (m,n) = eval [(Var "#in", Pair (N $ int2nat m) (N $ int2nat n))] plusExpr

test_succ :: Int -> (Val, Env)
test_succ m = eval [(Var "#in", N $ int2nat m)] succExpr

test_plusR :: (Int, Int) -> (Val, Env)
test_plusR (m,n) = eval [(Var "#in", Pair (N $ int2nat m) (N $ int2nat n))] plusRExpr
