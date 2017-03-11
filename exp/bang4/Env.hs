module Env (subs, insert, neutralize, popout) where
--
import Expr
--
-- name-based lookup
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
-- variable substitution
subs :: CtxSwitch -> Env -> VTerm -> Val
subs _ env (Lit val) = val
subs ctxSW env (Atom va) = raccess ctxSW env va
subs ctxSW env (Prod vt1 vt2) =
    Pr (subs ctxSW env vt1) (subs ctxSW env vt2)
subs ctxSW env (NatS vt) =
    let (N nat) = subs ctxSW env vt in (N $ S nat)
--
-- matchable insertion
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
--
-- neutralize variable from env
neutralize :: CtxSwitch -> Env -> VTerm -> Env
neutralize _ env (Lit _) = env
neutralize Linear (Env lis nls) (Atom va) =
    Env (filter ((/= va) . fst) lis) nls
neutralize Normal (Env lis nls) (Atom va) =
    Env lis (filter ((/= va) . fst) nls)
neutralize ctxSW env (Prod vt1 vt2) =
    neutralize ctxSW (neutralize ctxSW env vt1) vt2
neutralize ctxSW env (NatS vt) =
    neutralize ctxSW env vt
--
-- pop out variable
popout :: CtxSwitch -> Env -> VTerm -> (Val, Env)
popout ctxSW env vt =
    ( subs ctxSW env vt
    , neutralize ctxSW env vt)
