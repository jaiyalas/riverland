module Env where
--
import Expr
--

-- name based random access(?)
raccess :: CtxSwitch -> Env -> Var -> Val
raccess Linear (Env ((v2, val) : lis) nls) v1
    | v1 == v2 = val
    | otherwise = raccess Linear (Env lis nls) v1
--
raccess Linear (Env [] _) v1 = error $
    "<<raccess | Environment exhausted>>\n"++
    "\tCannot find (" ++ (show v1) ++ ") in linear context."
--
raccess Normal (Env lis ((v2, val) : nls)) v1
    | v1 == v2 = val
    | otherwise = raccess Normal (Env lis nls) v1
--
raccess Normal (Env _ []) v1 = error $
    "<<raccess | Environment exhausted>>\n"++
    "\tCannot find (" ++ (show v1) ++ ") in normal context."
--
raccessVT :: CtxSwitch -> Env -> VTerm -> Val
raccessVT _ env (Lit val) = val
raccessVT ctxSW env (Atom va) = raccess ctxSW env va
raccessVT ctxSW env (Prod vt1 vt2) =
    Pr (raccessVT ctxSW env vt1) (raccessVT ctxSW env vt2)
raccessVT ctxSW env (NatS vt) =
    let (N nat) = raccessVT ctxSW env vt in (N $ S nat)
--
-- structural-matchable based random access(?)
insert :: CtxSwitch -> Env -> MTerm -> Val -> Env
insert _ env (Lit _) _ = env -- value is unwritable
insert Linear (Env ls ns) (Atom (Mat name)) val =
    Env (((Var name, val) :) $ filter ((/= Var name).fst) ls) ns
insert Normal (Env ls ns) (Atom (Mat name)) val =
    Env ls (((Var name, val) :) $ filter ((/= Var name).fst) ns)
insert ctxSW env (Prod mt1 mt2) (Pr v1 v2) =
    insert ctxSW (insert ctxSW env mt1 v1) mt2 v2
insert ctxSW env (NatS mt) (N (S nat)) = insert ctxSW env mt (N nat)
--
insert ctxSW env mt v = error $
    "<<insert | Unknown>>\n"++
    "\tCannot insert \"" ++ (show mt) ++ "/" ++ (show v) ++
    "\" in "++(show ctxSW)++" context."
