module Eval where
--
import Expr
import Env
import Func
import Pat
-- rm: returned env
eval :: Env -> Expr -> (Val, Env)
--
eval env (Term vt) = (raccessVT Linear env vt, env)
--
-- del?
eval env (Lambda mt body) = (Closure env (Lambda mt body), env)
--
eval env (Pair e1 e2) =
    let (v1, env1) = eval env e1
        (v2, env2) = eval env e2
    in (Pr v1 v2, env)
--
-- LetRecIn?
eval env (LetIn mt (Left (Lambda argMT body)) e) =
    let newEnv = insert Normal env mt (Closure env (Lambda argMT body))
    in eval newEnv e
--
eval env (LetIn mt (Left localExp) e) =
    let (val, env') = eval env localExp
        newEnv = insert Linear env' mt val
    in eval newEnv e
--
eval env (LetIn mt (Right (fname, vt)) e) =
    let -- get function as f
        fun@(Closure fenv (Lambda argMT fbody)) = raccessVT Normal env (var fname)
        -- get args
        argVal = raccessVT Linear env vt
        -- put args to local env
        argedEnv = insert Linear fenv argMT argVal
        -- put f back to local env
        recurEnv = insert Normal argedEnv (mat fname) fun
        -- eval f with local env
        (res, _) = eval recurEnv fbody
        -- restore env and put result into it
        newEnv = insert Linear env mt res
    in eval newEnv e
eval env (DupIn (Prod (Atom (Mat ma1)) (Atom (Mat ma2))) (Atom va) e) =
        let val = raccessVT Linear env (Atom va)
            newEnv = (Var ma2, val) `consL` ((Var ma1, val) `consL` env)
        in eval newEnv e
--
eval env (Match vt cases) =
    let val = raccessVT Linear env vt
        (env2, e) = matching val cases
    in eval (env2 `mappend` env) e
-- 整理
eval env (MatEq vt case1 case2) = case raccessVT Linear env vt of
    (Pr val1 val2) ->
        if val1 == val2
            then case case1 of
                (Atom (Mat ma) :~> e1) ->
                    eval ((Var ma, val2) `consL` env) e1
                (NatS (Atom (Mat ma)) :~> e2) ->
                    eval ((Var ma, redN val1) `consL` env) e2
                (pat :~> _) -> error $
                    "<<eval | Illegal pattern>>\n"++
                    "\t"++(show pat)++" is illegal within MatEq-(case1)"
            else case case2 of
                (Prod mt1 mt2 :~> e1) ->
                    let newEnv = insert Linear (insert Linear env mt1 val1) mt2 val2
                    in eval newEnv e1
                (pat :~> _) -> error $
                    "<<eval | Illegal pattern>>\n"++
                    "\t"++(show pat)++" is illegal within MatEq-(case2)"
    otherwise -> error $
        "<<eval | Illegal value>>\n"++
        "\t"++(show vt)++" is illegal within MatEq"
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --
eval _ _ = error $
    "<<eval | Unknown>>\n"++
    "eval failed"
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --
