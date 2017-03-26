module Rval2 where
--
import Expr
import Env
import Func
import Pat
import Eval

import Debug.Trace (traceShow)

--
{-
`eval :: Env -> Expr -> (Val, Env)`

The returned `Env` is just a convenient result.
Ideally `eval` function should return `Val` only.

Correspondingly `rval` should have type as `Val -> Expr -> Env`.
Howere it will be much easier to compute by having a working environment.
Notice that this input `env` is not the very same environment that returned by `eval`.
-}
--
rval :: (Val, Env) -> Expr -> Env
--
rval (v, env) (Term vt) = insert Linear env (vmTrans vt) v
--
rval (v, env) (Lambda mt body) = env
--
rval (Pr v1 v2, env) (Pair e1 e2) =
    let env1 = rval (v1, env) e1
        env2 = rval (v2, env) e2
    in env1 `mappend` env2
--
rval (v, env) (RecIn mt localExp nextExp) = case localExp of
    (Lambda fpara fbody) ->
        let funR = Closure (insert Normal env mt funR) (Lambda fpara fbody)
            newEnv = insert Normal env mt funR
        in rval (v, newEnv) nextExp
    _ -> rval (v, env) (LetIn mt (Left localExp) nextExp)
--
rval (v, env) (LetIn mt (Left (Lambda fpara fbody)) nextExp) =
    let newEnv = insert Normal env mt $
                    Closure env (Lambda fpara fbody)
    in rval (v, newEnv) nextExp
--
rval (v, env) (LetIn mt (Left localExp) nextExp) =
    let nextEnv = rval (v, env) nextExp
        v2 = subs Linear nextEnv (mvTrans mt)
    in rval (v2, nextEnv) localExp
--
rval (v, env) (LetIn mt (Right (fname, vt)) nextExp) =
    let (Closure fenv (Lambda fmt fbody)) = subs Normal env (var fname)
        nextEnv = rval (v, env) nextExp
        fout = subs Linear nextEnv (mvTrans mt)
        localEnv = rval (fout, fenv) fbody
        fin = subs Linear localEnv (mvTrans fmt)
    in insert Linear nextEnv (vmTrans vt) fin
--
rval (v, env) (DupIn (Prod mtl mtr) vt nextExp) =
    let nextEnv = rval (v, env) nextExp
        lVal = subs Linear nextEnv (mvTrans mtl)
        rVal = subs Linear nextEnv (mvTrans mtr)
    in if lVal == rVal
        then insert Linear nextEnv (vmTrans vt) rVal
        else error $
            "<<rval | Illegal values>>\n"++
            "\tReversing DupIn failed with: "++
            "\t\t("++(show lVal)++"=/="++(show rVal)++")"

--
rval (v, env) (Match vt []) = error $
    "<<rval | Case exhausted>>\n"++
    "\tNo pattern can be rev-matched"
rval (v, env) (Match vt (mt :~> cexp : cases))
    | oracle v cexp =
        let midEnv = rval (v, env) cexp
            patVal = subs Linear midEnv (mvTrans mt)
            finEnv = insert Linear midEnv (vmTrans vt) patVal
        in
            --  traceShow mt $
            --  traceShow "> " $
            --  traceShow (getLCtx finEnv) $
             finEnv
    | otherwise = rval (v, env) (Match vt cases)
--
rval (v, env) (MatEq vt (mt1 :~> cexp1) (mt2 :~> cexp2))
    | oracle v cexp1 =
        let midEnv = rval (v, env) cexp1
            patVal = subs Linear midEnv (mvTrans mt1)
        in insert Linear midEnv (vmTrans vt) (Pr patVal patVal)
    | oracle v cexp2 = -- as normal r-matching
        let midEnv = rval (v, env) cexp2
            patVal = subs Linear midEnv (mvTrans mt2)
        in insert Linear midEnv (vmTrans vt) patVal
    | otherwise = error $
        "<<rval | Case exhausted>>\n"++
        "\tNo pattern can be found in MatEq"
    -- rval (v, env) (Match vt [case1,case2])
rval _ _ = error $
    "<<rval | Unknown>>"
--
{-
The `oracle` is an extension of `rMatch`.
`oracle` allow to r-matching upon expr-level.
-}
oracle :: Val -> Expr -> Bool
oracle (Pr vl vr) (DupIn mt vt expr)
    | vl == vr = rMatch (Pr vl vr) (dss expr)
    | otherwise = False
oracle v expr = -- rMatch v (dss expr)
    let x = traceShow v $ traceShow (dss expr) $ 1
    in x `seq` (\ a -> rMatch v (dss expr)) x

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
