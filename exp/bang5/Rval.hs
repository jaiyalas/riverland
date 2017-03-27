module Rval where
--
import Expr
import Env
import Func
import Match
--

--
{-
The `oracle` is an extension of `revMatch`.
`oracle` allow to r-matching upon expr-level.
-}
oracle :: Val -> Expr -> Bool
oracle (Pr vl vr) (DupIn mt vt expr)
    | vl == vr = rMatch (Pr vl vr) (dss expr)
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
