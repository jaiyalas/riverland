module Rval where
--
import Expr
import Env
import Func
import Pat
import Eval

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
    undefined
    -- let env1 = rval (v1, env) e1
    --     env2 = rval (v2, env) e2
    -- in env1 `mappend` env2
--
rval (v, env) (RecIn mt localExp nextExp) =
    undefined
--     let midEnv = rval (v, env) nextExp
--     in neutralize Normal midEnv (mvTrans mt)
-- --

-- in fact, this is incorrect
rval (v, env) (LetIn mt (Left (Lambda fpara fbody)) nextExp) =
    undefined

rval (v, env) (LetIn mt (Left localExp) nextExp) =
    undefined

-- -- application: 2 expr / 2 variable / 2 Lit
rval (v, env) (LetIn mt (Right (fname, vt)) nextExp) =
    undefined

-- there is a catch: DupIn allows only non-function
rval (v, env) (DupIn (Prod mtl mtr) vt nextExp) =
    undefined

--
rval (v, env) (Match vt []) = error $
    "<<rval | Case exhausted>>\n"++
    "\tNo pattern can be rev-matched"
rval (v, env) (Match vt (mt :~> cexp : cases)) = if oracle v cexp
    then let midEnv = rval (v, env) cexp
             (patVal, finEnv) = popout Linear midEnv (mvTrans mt)
         in insert Linear finEnv (vmTrans vt) patVal
    else rval (v, env) (Match vt cases)
--
rval (v, env) (MatEq vt case1 case2) =
    rval (v, env) (Match vt [case1,case2])
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
