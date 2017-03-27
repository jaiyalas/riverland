module Eval where
--
import Expr
import Env
import Prelude
import Match
--
eval :: Env -> Expr -> (Val, Env)
--
-- Term VTerm
eval env (Term vt) = undefined
-- Pair Expr Expr
eval env (Pair e1 e2) = undefined
-- Lambda MTerm Expr
eval env (Lambda mt body) = undefined
-- --
-- AppIn MTerm FApp Expr
eval env (AppIn mt (fname, vt) next) = undefined
-- LetIn MTerm Expr Expr
eval env (LetIn mt localExpr next) = undefined
eval env (LetIn mt (Lambda fmt fbody) next) = undefined
-- DupIn MTerm VTerm Expr
eval env (DupIn mt vt next) = undefined
-- --
-- Match VTerm [Case]
eval env (Match vt cases) = undefined
-- MatEq VTerm Case Case
eval env (MatEq vt case1 case2) = undefined
--
eval _ _ = error $
    "<< eval | Unknown >>\n"++
    "eval failed"
