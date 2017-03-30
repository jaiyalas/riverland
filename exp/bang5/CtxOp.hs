module CtxOp (subs, insert, neutralize, popout) where
--
import Typ
import Env
import Expr
--


-- Reader Context



--
-- variable substitution
subs :: CtxSwitch -> Context -> VTerm -> (Val, Typ)
subs _ env (Lit val) = val
subs ctxSW env (Atom va) = lookupCtx ctxSW env va
subs ctxSW env (Prod vt1 vt2) =
    Pr (subs ctxSW env vt1) (subs ctxSW env vt2)
subs ctxSW env (NatS vt) =
    let (N nat) = subs ctxSW env vt in (N $ S nat)
subs ctxSW env (NatZ) = N Z
--

-- matchable insertion
insert :: CtxSwitch -> Context -> MTerm -> Val -> Context
insert _ env (Lit _) _ = env -- value is unwritable
insert Linear (Env ls ns) (Atom (Mat name)) val =
    Env (((Var name, val) :) $ filter ((/= Var name).fst) ls) ns
insert Normal (Env ls ns) (Atom (Mat name)) val =
    Env ls (((Var name, val) :) $ filter ((/= Var name).fst) ns)
insert ctxSW env (Prod mt1 mt2) (Pr v1 v2) =
    insert ctxSW (insert ctxSW env mt1 v1) mt2 v2
insert ctxSW env (NatS mt) (N (S nat)) = insert ctxSW env mt (N nat)
-- NatZ included
insert ctxSW env mt v = error $
    "<< insert | Unknown >>\n"++
    "\tCannot insert \"" ++ (show mt) ++ "/" ++ (show v) ++
    "\" in "++(show ctxSW)++" context."
--
-- neutralize variable from env
neutralize :: CtxSwitch -> Context -> VTerm -> Context
neutralize Linear (Env lis nls) (Atom va) =
    Env (filter ((/= va) . fst) lis) nls
neutralize Normal (Env lis nls) (Atom va) =
    Env lis (filter ((/= va) . fst) nls)
neutralize ctxSW env (Prod vt1 vt2) =
    neutralize ctxSW (neutralize ctxSW env vt1) vt2
neutralize ctxSW env (NatS vt) =
    neutralize ctxSW env vt
-- NatZ and Lit included
neutralize _ env _ = env
--
-- pop out variable
popout :: CtxSwitch -> Context -> VTerm -> (Val, Context)
popout ctxSW env vt =
    ( subs ctxSW env vt
    , neutralize ctxSW env vt)
