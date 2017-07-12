module Eval (eval) where
--
import Types
import Expr
import Ctx
import CtxOp
import Match
--
import Control.Monad.Reader
--
eval :: Expr -> Reader (Ctx Var Val) Val
--
-- Term VTerm
eval (Term vt) = asks (subs Linear vt)
-- Pair Expr Expr
eval (Pair e1 e2) = do
    v1 <- eval e1
    v2 <- eval e2
    return $ Pr v1 v2
-- Lambda MTerm Expr
eval fun@(Lambda _ _ _) = do
    ctx <- ask
    return $ Closure ctx fun
-- --
-- AppIn MTerm FApp Expr
eval (AppIn mt (fname, vt) next) = do
    (Closure fenv (Lambda fmt ty fbody)) <- asks (subs Normal (var fname))
    argv <- asks (subs Linear vt)
    resv <- local (\_ -> insert Linear fmt argv fenv) (eval fbody)
    local (insert Linear mt resv) (eval next)
-- LetIn MTerm Expr Expr
eval (LetIn mt localExpr next) = do
    x <- eval localExpr
    case x of
        fun@(Closure fenv fbody) -> do
            let funR = Closure (insert Normal mt funR fenv) fbody
            local (insert Normal mt funR) (eval next)
        val -> local (insert Linear mt val {-????-}) (eval next)


    -- case eval env localExpr of
    --     (fun@(Closure fenv fbody), _) ->
    --         let funR = Closure (insert Normal fenv mt funR) fbody
    --         in eval (insert Normal env mt funR) next
    --     (val, env') -> eval (insert Linear env' mt val) next

-- DupIn MTerm VTerm Expr
eval (DupIn mt vt next) = case mt of
    (Prod (Atom (Mat ma1)) (Atom (Mat ma2))) -> do
        val <- asks (subs Linear vt)
        let update = (insert Linear (mat ma2) val)
                   . (insert Linear (mat ma1) val)
        local update (eval next)
    _ -> error $
        "<< eval | Duplication failed >>\n"++
        "\tmatchables \""++(show mt)++"\" is illegal for DupIn"
-- --
-- Match VTerm [Case]
eval (Match vt cases) = do
    val <- asks (subs Linear vt)
    let (newLocalCtx, next) = matching val cases
    local (newLocalCtx `mappend`) (eval next)
-- MatEq VTerm Case Case
eval (MatEq vt caseEq caseNEq) = do
    val <- asks (subs Linear vt)
    case val of
        (Pr v1 v2) -> if v1 == v2
            then eval (Match (Lit v1) [caseEq])
            else eval (Match (Prod (Lit v1) (Lit v2)) [caseNEq])
        _ -> error $
            "<<eval | Illegal value>>\n"++
            "\t"++(show vt)++" is illegal for MatEq"
-- --
-- -- redundant, told by ghc..
-- eval _ _ = error $
--     "<< eval | Unknown >>\n"++
--     "eval failed"
--
