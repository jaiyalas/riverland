module CtxOpT where
--
import Types
import Ctx
import Expr
--
typeOf :: Val -> Typ
typeOf (N _) = TypNat
typeOf (B _) = TypBool
typeOf (Pr v1 v2) = (typeOf v1) `times` (typeOf v2)
typeOf (Closure ctx (Lambda mt ty e)) = error "oops" -- TypFunc ty (check e)

-- variable substitution
subsT :: CtxSwitch -> Ctx Var Typ -> VTerm -> Typ
subsT _ env (Lit val) = typeOf val
subsT ctxSW env (Atom va) = lookupCtx ctxSW env va
subsT ctxSW env (Prod vt1 vt2) =
    (subsT ctxSW env vt1) `times` (subsT ctxSW env vt2)
subsT ctxSW env (NatS vt) = case subsT ctxSW env vt of
    TypNat -> TypNat
    _ -> error "type error"
subsT ctxSW env (NatZ) = TypNat

-- matchable insertion
insertT :: CtxSwitch -> Ctx Var Typ -> MTerm -> Typ -> Ctx Var Typ
insertT _ env (Lit _) _ = env -- value is unwritable
insertT Linear (Ctx ls ns) (Atom (Mat name)) vt =
    Ctx (((Var name, vt) :) $ filter ((/= Var name).fst) ls) ns
insertT Normal (Ctx ls ns) (Atom (Mat name)) vt =
    Ctx ls (((Var name, vt) :) $ filter ((/= Var name).fst) ns)
insertT ctxSW env (Prod mt1 mt2) (TypProd t1 t2) =
    insertT ctxSW (insertT ctxSW env mt1 t1) mt2 t2
insertT ctxSW env (NatS mt) t = insertT ctxSW env mt t
-- NatZ included
insertT ctxSW env mt v = error $
    "<< insert | Unknown >>\n"++
    "\tCannot insert \"" ++ (show mt) ++ "/" ++ (show v) ++
    "\" in "++(show ctxSW)++" context."
