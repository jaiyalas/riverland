module Eval where
--
import Expr
import Env
import Func
import Pat
--
eval :: Env -> Expr -> (Val, Env)
--
eval env (Term vt) = reveal Linear env vt

eval env (Lambda mt body) = (Closure mt body, env)
--
eval env (LetIn mt (Left (Lambda localmt body)) e) =
    let newEnv = update Normal env mt (Closure localmt body)
    in eval newEnv e
-- for not lambda
eval env (LetIn mt (Left localExp) e) =
    let (val, env') = eval env localExp
        newEnv = update Linear env' mt val
    in eval newEnv e
--
eval env (LetIn mt (Right (funame, vt)) e) =
    let (Closure (Atom (Mat ma)) fbody, _) = reveal Normal env (var funame)
        (argVal, env') = reveal Linear env vt
        -- new linear context for lambda applicaion..
        localEnv = Env [(Var ma, argVal)] (getNCtx env)
        (res, _) = eval localEnv fbody
        newEnv = update Linear env' mt res
    in eval newEnv e
eval env (DupIn (Prod (Atom (Mat ma1)) (Atom (Mat ma2))) (Atom va) e) =
        let (val, env') = raccess Linear env va
            newEnv = (Var ma2, val) `consL` ((Var ma1, val) `consL` env')
        in eval newEnv e
--
eval env (Match vt cases) =
    let (val, env1) = reveal Linear env vt
        (env2, e) = matching val cases
    in eval (env1 `mappend` env2) e
--
eval env (MatEq vt case1 case2) = case reveal Linear env vt of
    ((Pair val1 val2), env2) ->
        if val1 == val2
            then case case1 of
                (Atom (Mat ma) :~> e1) ->
                    eval ((Var ma, val2) `consL` env2) e1
                (NatS (Atom (Mat ma)) :~> e2) ->
                    eval ((Var ma, redN val1) `consL` env2) e2
                (pat :~> _) -> error $
                    "<<eval | Illegal pattern>>\n"++
                    "\t"++(show pat)++" is illegal within MatEq-(case1)"
            else case case2 of
                (Prod mt1 mt2 :~> e1) ->
                    let newEnv = update Linear (update Linear env2 mt1 val1) mt2 val2
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
