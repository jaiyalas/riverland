module Eval (eval) where
--
import Expr
import Ctx
import CtxOp
import Func
import Match
--
eval :: Ctx Var Val -> Expr -> (Val, Ctx Var Val)
--
-- Term VTerm
eval env (Term vt) = (subs Linear env vt, env)
-- Pair Expr Expr
eval env (Pair e1 e2) =
    let (v1, env1) = eval env e1
        (v2, env2) = eval env e2
    in (Pr v1 v2, env1 `mappend` env2)
-- Lambda MTerm Expr
eval env fun@(Lambda _ _) = (Closure env fun, env)
-- --
-- AppIn MTerm FApp Expr
eval env (AppIn mt (fname, vt) next) =
    let fun@(Closure fenv (Lambda fmt fbody)) = subs Normal env (var fname)
        argv = subs Linear env vt
        (resv, _) = eval (insert Linear fenv fmt argv) fbody
        nextEnv = insert Linear env mt resv
    in eval nextEnv next
-- LetIn MTerm Expr Expr
eval env (LetIn mt localExpr next) =
    case eval env localExpr of
        (fun@(Closure fenv fbody), _) ->
            let funR = Closure (insert Normal fenv mt funR) fbody
            in eval (insert Normal env mt funR) next
        (val, env') -> eval (insert Linear env' mt val) next
-- DupIn MTerm VTerm Expr
eval env (DupIn mt vt next) = case mt of
    (Prod (Atom (Mat ma1)) (Atom (Mat ma2))) ->
        let val = subs Linear env vt
            nextEnv = (Var ma2, val) `consL` ((Var ma1, val) `consL` env)
        in eval nextEnv next
    _ -> error $
        "<< eval | Duplication failed >>\n"++
        "\tmatchables \""++(show mt)++"\" is illegal for DupIn"
-- --
-- Match VTerm [Case]
eval env (Match vt cases) =
    let v = subs Linear env vt
        (newEnv, next) = matching v cases
    in eval (newEnv `mappend` env) next
-- MatEq VTerm Case Case
eval env (MatEq vt caseEq caseNEq) = case subs Linear env vt of
    (Pr v1 v2) -> if v1 == v2
        then eval env (Match (Lit v1) [caseEq])
        else eval env (Match (Prod (Lit v1) (Lit v2)) [caseNEq])
    _ -> error $
        "<<eval | Illegal value>>\n"++
        "\t"++(show vt)++" is illegal for MatEq"
-- --
-- -- redundant, told by ghc..
-- eval _ _ = error $
--     "<< eval | Unknown >>\n"++
--     "eval failed"
--
