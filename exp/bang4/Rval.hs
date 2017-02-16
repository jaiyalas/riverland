module Rval where
--
import Expr
import Env
import Func
import Pat
--
rval :: (Val, Env) -> Expr -> Env
--
rval (v, env) (Term vt) = insert Linear env (vmTrans vt) v
--
rval (Closure _ _, env) (Lambda mt body) = env
--
rval (v, env) (Pair e1 e2) =
    let (v1, env1) = eval env e1
        (v2, env2) = eval env e2
    in (Pr v1 v2, env)

-- -- -- -- -- -- -- --

--
rval (v, env) (LetIn (Atom (Mat fName)) (Left (Lambda localmt body)) e) =
    forceVarRM Normal (rval (v, env) e) (Var fName)
--
rval (v, env) (LetIn mt (Left e') e) =
    let midEnv = rval (v, env) e
        (v', env') = reveal Linear midEnv (mvTrans mt)
    in rval (v', env') e'
-- application: 2 expr / 2 variable / 2 Lit
rval (v, env) (LetIn mt (Right (fname, vt)) e) =
    let midEnv = rval (v, env) e
        (val, env') = reveal Linear midEnv (mvTrans mt)
        (Closure fmt fbody, _) = reveal Normal env (var fname)
        -- clear local env?
        localEnv = rval (val, env') fbody
        -- ???
        (vFunIn, _)= reveal Linear localEnv (mvTrans fmt)
    in update Linear env' (vmTrans vt) vFunIn
--




--
rval (v, env) (Match vt []) = error $
    "<<rval | Case exhausted>>\n"++
    "\tNo pattern can be rev-matched"
rval (v, env) (Match vt (mt :~> cexp : cases)) =
    if oracle v cexp
        then let midEnv = rval (v, env) cexp
                 (patVal, finEnv) = reveal Linear midEnv (mvTrans mt)
             in update Linear finEnv (vmTrans vt) patVal
        else rval (v, env) (Match vt cases)
--
rval (v, env) (DupIn (Prod mtl mtr) vt e) =
    let midEnv = rval (v, env) e
        (lVal, midEnv2) = reveal Linear midEnv (mvTrans mtl)
        (rVal, finEnv) = reveal Linear midEnv2 (mvTrans mtr)
    in if lVal == rVal
        then update Linear finEnv (vmTrans vt) rVal
        else error $
            "<<rval | Illegal values>>\n"++
            "\tReversing DupIn failed with: "++
            "\t\t("++(show lVal)++"=/="++(show rVal)++")"
rval (v, env) (MatEq vt case1 case2) =
    rval (v, env) (Match vt [case1,case2])
rval _ _ = error $
    "<<rval | Unknown>>"


{-
The `oracle` is an extension of `rMatch`.
`oracle` allow to r-matching upon expr-level.
-}
oracle :: Val -> Expr -> Bool
oracle (Pair vl vr) (DupIn mt vt expr)
    | vl == vr = rMatch (Pair vl vr) (dss expr)
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
rMatch (Pair v1 v2) (Prod vt1 vt2) =
    (rMatch v1 vt1) && (rMatch v2 vt2)
rMatch _ _ = False

-- headConstructor, aka de-structural-syntax
dss :: Expr -> VTerm
dss (Term vt) = vt
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
