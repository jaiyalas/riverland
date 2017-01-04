module Eval where
--
import Expr
import Env
import Pat
--
eval :: Env -> Expr -> (Val, Env)
--
eval env (Term vt)    = reveal env vt
--
eval env (LetIn mt (Left vt) e) =
    let (val, env') = reveal env vt
        newEnv = update env' mt val
    in eval newEnv e
--
eval env (LetIn mt (Right (funame, vt)) e) =
    let (Closure fbody, _) = peek env (var funame)
        (argVal, env') = reveal env vt
        localEnv = Env [(Var "#0", argVal)] (getNlCtx env)
        -- localEnv = update env' (mat "#0") argVal
        (res, _) = eval localEnv fbody
        newEnv = update env' mt res
    in eval newEnv e
--
eval env (DupIn (Prod (Atom (Mat ma1)) (Atom (Mat ma2))) (Atom va) e) =
        let (val, env') = takeout env va
            newEnv = (Var ma2, val) `consL` ((Var ma1, val) `consL` env')
        in eval newEnv e
--
eval env (Match vt cases) =
    let (val, env1) = reveal env vt
        (env2, e) = matching val cases
    in eval (env1 `mappend` env2) e
--
eval env (MatEq vt case1 case2) = case reveal env vt of
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
                    let newEnv = update (update env2 mt1 val1) mt2 val2
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
