module CtxOp where
--
import Types
import Ctx
import Expr
--
typeOf :: Val -> Typ
typeOf (N _) = TypNat
typeOf (B _) = TypNat
typeOf (Pr v1 v2) = TypProd (typeOf v1) (typeOf v2)
typeOf (Closure ctx (Lambda mt ty e)) = TypFunc ty undefined

-- variable substitution
subs :: CtxSwitch -> Ctx Var (Val, Typ) -> VTerm -> (Val, Typ)
subs _ env (Lit val) = (val, typeOf val)
subs ctxSW env (Atom va) = lookupCtx ctxSW env va
subs ctxSW env (Prod vt1 vt2) =
    (subs ctxSW env vt1) `times` (subs ctxSW env vt2)
subs ctxSW env (NatS vt) =
    let (N nat,t) = subs ctxSW env vt
    in (N $ S nat, t)
subs ctxSW env (NatZ) = (N Z, TypNat)

subsT :: CtxSwitch -> Ctx Var Typ -> VTerm -> Typ
subsT _ env (Lit val) = typeOf val
subsT ctxSW env (Atom va) = lookupCtx ctxSW env va
subsT ctxSW env (Prod vt1 vt2) =
    (subsT ctxSW env vt1) `times` (subsT ctxSW env vt2)
subsT ctxSW env (NatS vt) = case subsT ctxSW env vt of
    TypNat -> TypNat
    _ -> error "type error"
subsT ctxSW env (NatZ) = TypNat




subsVal cs ctx vt = fst $ subs cs ctx vt
subsTyp cs ctx vt = snd $ subs cs ctx vt


-- mt2val :: (MTerm, Val) -> Maybe Var
-- mt2val = vt2val . mvTrans
-- vt2val :: (VTerm, Val) -> Maybe Var
-- vt2val (Atom var, _) = Just var
-- vt2val (Prod t1 t2, Pr v1 v2) = Just $
--     ...
-- vt2val (NatS t1) = ...
-- vt2val _ = Nothing

-- matchable insertion
insert :: CtxSwitch -> Ctx Var (Val, Typ) -> MTerm -> (Val, Typ) -> Ctx Var (Val, Typ)
insert _ env (Lit _) _ = env -- value is unwritable
insert Linear (Ctx ls ns) (Atom (Mat name)) vt =
    Ctx (((Var name, vt) :) $ filter ((/= Var name).fst) ls) ns
insert Normal (Ctx ls ns) (Atom (Mat name)) vt =
    Ctx ls (((Var name, vt) :) $ filter ((/= Var name).fst) ns)
insert ctxSW env (Prod mt1 mt2) (Pr v1 v2, TypProd t1 t2) =
    insert ctxSW (insert ctxSW env mt1 (v1, t1)) mt2 (v2,t2)
insert ctxSW env (NatS mt) (N (S nat),t) = insert ctxSW env mt (N nat,t)
-- NatZ included
insert ctxSW env mt v = error $
    "<< insert | Unknown >>\n"++
    "\tCannot insert \"" ++ (show mt) ++ "/" ++ (show v) ++
    "\" in "++(show ctxSW)++" context."

insertVal cs ctx mt val = insert cs ctx mt (val, typeOf val)

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
