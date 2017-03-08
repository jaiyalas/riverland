module Rval where
--
import Expr
import Env
import Func
import Pat
import Eval

--
rval :: (Val, Env) -> Expr -> Env
--
rval (v, env) (Term vt) = insert Linear env (vmTrans vt) v
--
rval (v, env) (Lambda mt body) = env
--
rval (Pr v1 v2, env)  (Pair e1 e2) =
    let env1 = rval (v1, env) e1
        env2 = rval (v2, env) e2
    in env1 `mappend` env2

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- eval env (RecIn mt localExp e) = case eval env localExp of
--     (fun@(Closure fenv fbody), env') ->
--         let funR = Closure (insert Normal fenv mt funR) fbody
--         in eval (insert Normal env mt funR) e
--     (val, env')               -> eval (insert Linear env' mt val) e
-- --
-- eval env (LetIn mt (Left localExp) e) = case eval env localExp of
--     (fun@(Closure _ _), env') -> eval (insert Normal env  mt fun) e
--     (val              , env') -> eval (insert Linear env' mt val) e
-- --
-- eval env (LetIn mt (Right (fname, vt)) e) =
--     let fun@(Closure fenv (Lambda argMT fbody)) = subs Normal env (var fname)
--         argVal = subs Linear env vt
--         argedEnv = insert Linear fenv argMT argVal
--         (res, _) = eval argedEnv fbody
--         newEnv = insert Linear env mt res
--     in eval newEnv e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
rval (v, env) (RecIn mt localExp e) = undefined
--


-- eval env (LetIn mt (Left localExp) e) = case eval env localExp of
--     (fun@(Closure _ _), env') -> eval (insert Normal env  mt fun) e
--     (val              , env') -> eval (insert Linear env' mt val) e

-- well, there is a thing: should I REMOVE this stuff in env?
rval (v, env) (LetIn mt (Left (Lambda fpara fbody)) nextExp) =
    rval (v, env) nextExp
rval (v, env) (LetIn mt (Left localExp) nextExp) =
    let midEnv = rval (v, env) nextExp
        v2 = subs Linear midEnv (mvTrans mt)
    in rval (v2, midEnv) localExp



-- -- application: 2 expr / 2 variable / 2 Lit
-- rval (v, env) (LetIn mt (Right (fname, vt)) e) =
--     let midEnv = rval (v, env) e
--         (val, env') = subs Linear midEnv (mvTrans mt)
--         (Closure fmt fbody, _) = subs Normal env (var fname)
--         -- clear local env?
--         localEnv = rval (val, env') fbody
--         -- ???
--         (vFunIn, _)= subs Linear localEnv (mvTrans fmt)
--     in insert Linear env' (vmTrans vt) vFunIn
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

rval (v, env) (DupIn (Prod mtl mtr) vt e) =
    let midEnv = rval (v, env) e
        lVal = subs Linear midEnv (mvTrans mtl)
        rVal = subs Linear midEnv (mvTrans mtr)
    in if lVal == rVal
        then insert Linear midEnv (vmTrans vt) rVal
        else error $
            "<<rval | Illegal values>>\n"++
            "\tReversing DupIn failed with: "++
            "\t\t("++(show lVal)++"=/="++(show rVal)++")"
--
rval (v, env) (Match vt []) = error $
    "<<rval | Case exhausted>>\n"++
    "\tNo pattern can be rev-matched"
rval (v, env) (Match vt (mt :~> cexp : cases)) =
    if oracle v cexp
        then let midEnv = rval (v, env) cexp
                 (patVal, finEnv) = subs Linear midEnv (mvTrans mt)
             in insert Linear finEnv (vmTrans vt) patVal
        else rval (v, env) (Match vt cases)
--
rval (v, env) (MatEq vt case1 case2) =
    rval (v, env) (Match vt [case1,case2])
rval _ _ = error $
    "<<rval | Unknown>>"


{-
The `oracle` is an extension of `rMatch`.
`oracle` allow to r-matching upon expr-level.
-}
oracle :: Val -> Expr -> Bool
oracle (Pr vl vr) (DupIn mt vt expr)
    | vl == vr = rMatch (Pr vl vr) (dss expr)
    | otherwise = False
oracle v expr = rMatch v (dss expr)
-- reversed matching
rMatch :: Val -> VTerm -> Bool
rMatch (Closure _ _) _ = False
rMatch _ (Atom _) = True
-- 0 <m> 0
rMatch (N Z) (Lit (N Z)) = True
-- S n <m> S n
rMatch (N (S n)) (Lit (N (S m))) = rMatch (N n) (Lit (N m))
-- 0 <m> S n
rMatch (N Z) (NatS vt) = False
-- S n <m> S n
rMatch (N (S n)) (NatS vt) = rMatch (N n) vt
rMatch (B b) (Lit (B c)) = if b == c then True else False
rMatch (Pr v1 v2) (Prod vt1 vt2) =
    (rMatch v1 vt1) && (rMatch v2 vt2)
rMatch _ _ = False

-- headConstructor, aka de-structural-syntax
dss :: Expr -> VTerm
dss (Term vt) = vt
-- dss (RecIn ?) = ?
-- dss (Pair ?) = ?
dss (LetIn mt (Left vt) expr) = dss expr
dss (LetIn mt (Right fapp) expr) = dss expr
dss (DupIn mt vt expr) = dss expr
dss (Match vt cases) = error $
    "<<dss | Illegal syntax>>\n"++
    "\t\"Match\" cannot be DSS-fied"
dss (MatEq vt case1 case2) = error $
    "<<dss | Illegal syntax>>\n"++
    "\t\"MatEq\" cannot be DSS-fied"

-- a case-fliper will be helpful
