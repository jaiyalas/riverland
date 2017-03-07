module Eval where
--
import Expr
import Env
import Func
import Pat
-- rm: returned env
eval :: Env -> Expr -> (Val, Env)
--
eval env (Term vt) = (subs Linear env vt, env)
--
eval env (Lambda mt body) = (Closure env (Lambda mt body), env)
--
eval env (Pair e1 e2) =
    let (v1, env1) = eval env e1
        (v2, env2) = eval env e2
    in (Pr v1 v2, env)
--
eval env (RecIn mt localExp e) = case eval env localExp of
    (fun@(Closure fenv fbody), env') ->
        let funR = Closure (insert Normal fenv mt funR) fbody
        in eval (insert Normal env mt funR) e
    (val, env')               -> eval (insert Linear env' mt val) e
--
eval env (LetIn mt (Left localExp) e) = case eval env localExp of
    (fun@(Closure _ _), env') -> eval (insert Normal env  mt fun) e
    (val              , env') -> eval (insert Linear env' mt val) e
--
eval env (LetIn mt (Right (fname, vt)) e) =
    let fun@(Closure fenv (Lambda argMT fbody)) = subs Normal env (var fname)
        argVal = subs Linear env vt
        argedEnv = insert Linear fenv argMT argVal
        (res, _) = eval argedEnv fbody
        newEnv = insert Linear env mt res
    in eval newEnv e
eval env (DupIn (Prod (Atom (Mat ma1)) (Atom (Mat ma2))) (Atom va) e) =
        let val = subs Linear env (Atom va)
            newEnv = (Var ma2, val) `consL` ((Var ma1, val) `consL` env)
        in eval newEnv e
--
eval env (Match vt cases) =
    let val = subs Linear env vt
        (env2, e) = matching val cases
    in eval (env2 `mappend` env) e
--
eval env (MatEq vt caseEq caseNonEq) = case subs Linear env vt of
    (Pr val1 val2) -> if val1 == val2
        then eval env (Match (Lit val1) [caseEq])
        else eval env (Match (Prod (Lit val1) (Lit val2)) [caseNonEq])
    otherwise -> error $
        "<<eval | Illegal value>>\n"++
        "\t"++(show vt)++" is illegal for MatEq"
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --
eval _ _ = error $
    "<<eval | Unknown>>\n"++
    "eval failed"
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --
