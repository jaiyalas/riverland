module REval where
--
import Expr
import Ctx
import Func
import Pat
--

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
reval :: (Val, Env) -> Expr -> Env
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
reval (v, env) (Term vt) = updateMT env (vmTrans vt) v
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
reval (v, env) (LetIn mt (Left vt) e) =
    let midEnv = reval (v, env) e
        (val, env') = revealVT midEnv (mvTrans mt)
    in updateMT env' (vmTrans vt) val
reval (v, env) (LetIn mt (Right (fname, vt)) e) =
    let midEnv = reval (v, env) e
        (val, env') = revealVT midEnv (mvTrans mt)
        (Closure _ fbody, _) = revealVT prelude (var fname)
        funEnv = reval (val, []) fbody
        (vFunIn, _)= find funEnv (Var "#in")
    in updateMT env' (vmTrans vt) vFunIn
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
reval (v, env) (Match vt []) = error $ "No pattern can be rev-matched"
reval (v, env) (Match vt (mt :~> cexp : cases)) =
    -- if revMatch v (dss cexp)
    if revMatch_2Expr v cexp
        then let midEnv = reval (v, env) cexp
                 (patVal, finEnv) = revealVT midEnv (mvTrans mt)
             in updateMT finEnv (vmTrans vt) patVal
        else reval (v, env) (Match vt cases)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
reval (v, env) (DupIn (Prod mtl mtr) vt e) =
    let midEnv = reval (v, env) e
        (lVal, midEnv2) = revealVT midEnv (mvTrans mtl)
        (rVal, finEnv) = revealVT midEnv2 (mvTrans mtr)
    in if lVal == rVal
        then updateMT finEnv (vmTrans vt) rVal
        else error $ "Reversing DupIn failed with: "++
            "("++(show lVal)++","++(show rVal)++")"
reval (v, env) (MatEq vt case1 case2) =
    reval (v, env) (Match vt [case1,case2])
reval _ _ = error $ "rEval failed due to unidentified reason"


revMatch_2Expr :: Val -> Expr -> Bool
revMatch_2Expr (Pair vl vr) (DupIn mt vt expr)
    | vl == vr = revMatch (Pair vl vr) (dss expr)
    | otherwise = False
revMatch_2Expr v expr = revMatch v (dss expr)
--
revMatch :: Val -> VTerm -> Bool
--
revMatch (Closure _ _) _ = False
revMatch _ (Atom _) = True
-- # # # # # # # # # # # # # # # # # #
-- 0 <m> 0
revMatch (N Z) (Lit (N Z)) = True
-- S n <m> S n
revMatch (N (S n)) (Lit (N (S m))) = revMatch (N n) (Lit (N m))
-- 0 <m> S n
revMatch (N Z) (NatS vt) = False
-- S n <m> S n
revMatch (N (S n)) (NatS vt) = revMatch (N n) vt
-- # # # # # # # # # # # # # # # # # #
revMatch (B b) (Lit (B c)) = if b == c then True else False
-- # # # # # # # # # # # # # # # # # #
revMatch (Pair v1 v2) (Prod vt1 vt2) =
    (revMatch v1 vt1) && (revMatch v2 vt2)
-- # # # # # # # # # # # # # # # # # #
revMatch _ _ = False

-- headConstructor, aka de-structural-syntax
dss :: Expr -> VTerm
dss (Term vt) = vt
dss (LetIn mt (Left vt) expr) = dss expr
dss (LetIn mt (Right fapp) expr) = dss expr
dss (DupIn mt vt expr) = dss expr
dss (Match vt cases) = error $ "\"Match\" cannot be DSS-fied"
dss (MatEq vt case1 case2) = error $ "\"MatEq\" cannot be DSS-fied"

-- a case-fliper will be helpful


-- envGen :: ???

testR_succ :: Int -> Env
testR_succ n = reval ( N $ int2nat n, []) succExpr

testR_plus :: (Int, Int) -> Env
testR_plus (m, n) = reval ( Pair (N $ int2nat m) (N $ int2nat n)
                          , []) plusExpr
