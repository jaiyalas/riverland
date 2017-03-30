module Rval where
--
import Expr
import Ctx
import CtxOp
import Func
import Match
--
rval :: Ctx Var Val -> Val -> Expr -> Ctx Var Val
-- Term VTerm
rval env v (Term vt) =
    insert Linear env (vmTrans vt) v
-- Pair Expr Expr
rval env (Pr v1 v2) (Pair e1 e2) =
    let env1 = rval env v1 e1
        env2 = rval env v1 e2
    in env1 `mappend` env2
rval env v (Pair e1 e2) = error $
    "<< rval | illegal syntax (Pair) >>\n" ++
    "\t"++(show v)++" doesn't match to "++(show (Pair e1 e2))
-- Lambda MTerm Expr
rval env v (Lambda fmt fbody) = env
-- --
-- AppIn MTerm FApp Expr
rval env v (AppIn mt (fname, vt) next) =
    let (Closure fenv (Lambda fmt fbody)) = subs Normal env (var fname)
    in vmGenWith (rval env v next) (mvTrans mt) (vmTrans vt)
        (\fout ->
            subs Linear (rval fenv fout fbody) (mvTrans fmt))
    --     nextEnv = rval env v next
    --     fout = subs Linear nextEnv (mvTrans mt)
    --     localEnv = rval (fout, fenv) fbody
    --     fin = subs Linear localEnv (mvTrans fmt)
    -- in insert Linear nextEnv (vmTrans vt) fin
-- --
-- LetIn MTerm Expr Expr
-- !!! NOTICE !
-- !!! localExpr has diff assumption in eval/rval
-- !!! in here, it's expected to be Lambda as head
-- !!! but not in eval
rval env v (LetIn mt localExpr next) = case localExpr of
    fun@(Lambda fmt fbody) ->
        let funR = Closure (insert Normal env mt funR) fun
        in rval (insert Normal env mt funR) v next
    otherwise ->
        let nextEnv = rval env v next
            v2 = subs Linear nextEnv (mvTrans mt)
        in rval nextEnv v2 localExpr
-- DupIn MTerm VTerm Expr
rval env v (DupIn (Prod mtl mtr) vt next)
    | lv == rv = insert Linear nextEnv (vmTrans vt) rv
    | otherwise = error $
            "<< rval | illegal values (DupIn) >>\n"++
            "\tReversing DupIn failed with: "++
            "\t\t("++(show lv)++"=/="++(show rv)++")"
        where nextEnv = rval env v next
              lv = subs Linear nextEnv (mvTrans mtl)
              rv = subs Linear nextEnv (mvTrans mtr)
rval env v (DupIn mt vt next) = error $
    "<< rval | illegal syntax (DupIn) >>\n" ++
    "\t"++(show mt)++"is not a product"
-- --
-- Match VTerm [Case]
rval env v (Match vt []) = error $
    "<< rval | case exhausted (Match) >>"
rval env v (Match vt (mt :~> next : cases))
    | oracle v next =
        vmGen (rval env v next) (mvTrans mt) (vmTrans vt)
    | otherwise = rval env v (Match vt cases)
-- MatEq VTerm Case Case
rval env v (MatEq vt (mtEq :~> nextEq) (mtNEq :~> nextNEq))
    | oracle v nextEq =
        vmGenWith (rval env v nextEq)
            (mvTrans mtEq) (vmTrans vt) (\x-> Pr x x)
    | oracle v nextNEq =
        vmGen (rval env v nextNEq) (mvTrans mtNEq) (vmTrans vt)
    | otherwise = error "<< rval | case exhausted (MatEq) >>"
-- --
--
-- rval _ _ _ = error $
--     "<< rval | unknown >>"
-- --


{-
The `oracle` is an extension of `revMatch`.
`oracle` allow to r-matching upon expr-level.
-}
oracle :: Val -> Expr -> Bool
oracle (Pr vl vr) (DupIn mt vt expr)
    | vl == vr = revMatch (Pr vl vr) (dss expr)
    | otherwise = False
oracle v expr = revMatch v (dss expr)
-- --

-- reversed pattern matching
revMatch :: Val -> VTerm -> Bool
revMatch (B b) (Lit (B c)) =
    if b == c then True else False
-- 0 <m> 0
revMatch (N Z) (NatZ)      = True
revMatch (N Z) (Lit (N Z)) = True
-- S n <m> S n
revMatch (N (S n)) (NatS vt) =
    revMatch (N n) vt
revMatch (N (S n)) (Lit (N (S m))) =
    revMatch (N n) (Lit (N m))
-- pair
revMatch (Pr v1 v2) (Prod vt1 vt2) =
    (revMatch v1 vt1) && (revMatch v2 vt2)
-- irrefusable
revMatch _ (Atom _) = True
revMatch _ _ = False
-- --

-- headConstructor, aka de-structural-syntax
dss :: Expr -> VTerm
dss (Term vt) = vt
dss (Pair e1 e2) = Prod (dss e1) (dss e2)
dss (LetIn _ _ expr) = dss expr
dss (AppIn _ _ expr) = dss expr
dss (DupIn _ _ expr) = dss expr
dss (Match _ _) = error $
    "<<dss | Illegal syntax>>\n"++
    "\t\"Match\" cannot be DSS-fied"
dss (MatEq _ _ _) = error $
    "<<dss | Illegal syntax>>\n"++
    "\t\"MatEq\" cannot be DSS-fied"
-- --

-- find val by vt; and, create val by mt
vmGen :: Ctx Var Val -> VTerm -> MTerm -> Ctx Var Val
vmGen = \ env vt mt -> vmGenWith env vt mt id
vmGenWith :: Ctx Var Val -> VTerm -> MTerm -> (Val -> Val) -> Ctx Var Val
vmGenWith nev vt mt f =
    insert Linear nev mt $
    f $ subs Linear nev vt
