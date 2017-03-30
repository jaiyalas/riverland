module CtxOp where
--
import Types
import Ctx
import Expr
--
-- variable substitution
subs :: CtxSwitch -> Ctx Var Val -> VTerm -> Val
subs _ env (Lit val) = val
subs ctxSW env (Atom va) = lookupCtx ctxSW env va
subs ctxSW env (Prod vt1 vt2) =
    Pr (subs ctxSW env vt1) (subs ctxSW env vt2)
subs ctxSW env (NatS vt) =
    let (N nat) = subs ctxSW env vt in (N $ S nat)
subs ctxSW env (NatZ) = N Z
--

-- matchable insertion
insert :: CtxSwitch -> Ctx Var Val -> MTerm -> Val -> Ctx Var Val
insert _ env (Lit _) _ = env -- value is unwritable
insert Linear (Ctx ls ns) (Atom (Mat name)) val =
    Ctx (((Var name, val) :) $ filter ((/= Var name).fst) ls) ns
insert Normal (Ctx ls ns) (Atom (Mat name)) val =
    Ctx ls (((Var name, val) :) $ filter ((/= Var name).fst) ns)
insert ctxSW env (Prod mt1 mt2) (Pr v1 v2) =
    insert ctxSW (insert ctxSW env mt1 v1) mt2 v2
insert ctxSW env (NatS mt) (N (S nat)) = insert ctxSW env mt (N nat)
-- NatZ included
insert ctxSW env mt v = error $
    "<< insert | Unknown >>\n"++
    "\tCannot insert \"" ++ (show mt) ++ "/" ++ (show v) ++
    "\" in "++(show ctxSW)++" context."
--
-- -- neutralize variable from env
-- neutralize :: CtxSwitch -> Ctx a b -> VTerm -> Ctx a b
-- neutralize Linear (Ctx lis nls) (Atom va) =
--     Ctx (filter ((/= va) . fst) lis) nls
-- neutralize Normal (Ctx lis nls) (Atom va) =
--     Ctx lis (filter ((/= va) . fst) nls)
-- neutralize ctxSW env (Prod vt1 vt2) =
--     neutralize ctxSW (neutralize ctxSW env vt1) vt2
-- neutralize ctxSW env (NatS vt) =
--     neutralize ctxSW env vt
-- -- NatZ and Lit included
-- neutralize _ env _ = env
-- --
-- -- pop out variable
-- popout :: CtxSwitch -> Ctx a b -> VTerm -> (b, Ctx a b)
-- popout ctxSW env vt =
--     ( subs ctxSW env vt
--     , neutralize ctxSW env vt)
