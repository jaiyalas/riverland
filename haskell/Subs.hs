module Subs where
import Expr
--
freeVar :: Expr -> [FName]
freeVar (Term vt) =
    freeVar' vt
freeVar (LetIn _ (Left vt) e) =
    freeVar' vt ++ freeVar e
freeVar (LetIn _ (Right (_, vts)) e) =
    (concat.fmap freeVar') vts ++ freeVar e
freeVar (DupIn _ vt e) =
    freeVar' vt ++ freeVar e
freeVar (Match vt cs) =
    freeVar' vt ++ (concat $ map (freeVar.uncaseExpr) cs)
freeVar (MatEq (vt1, vt2) (_ :--> e1) (_ :--> e2)) =
    freeVar' vt1 ++ freeVar' vt2 ++ freeVar e1 ++ freeVar e2
--
freeVar' :: VTerm -> [FName]
freeVar' (Lit  v)   = []
freeVar' (Atom (Var s)) = [s]
freeVar' (Prod t1 t2)   = freeVar' t1 ++ freeVar' t2
freeVar' (Fst  t)       = freeVar' t
freeVar' (Snd t)        = freeVar' t
--
freeMat :: Expr -> [FName]
freeMat (Term _) = []
freeMat (LetIn mt _ e) =
    freeMat' mt ++ freeMat e
freeMat (DupIn mt _ e) =
    freeMat' mt ++ freeMat e
freeMat (Match _ cs) =
    concat $ map freeMat_case cs
freeMat (MatEq _ c1 c2) =
    freeMat_case c1 ++ freeMat_case c2
--
freeMat' :: MTerm -> [FName]
freeMat' (Lit  v)   = []
freeMat' (Atom (Mat s)) = [s]
freeMat' (Prod t1 t2)   = freeMat' t1 ++ freeMat' t2
freeMat' (Fst  t)       = freeMat' t
freeMat' (Snd t)        = freeMat' t
--
freeMat_case :: Case -> [FName]
freeMat_case (mt :--> e) = freeMat' mt ++ freeMat e
--
subs :: Var -> Dom -> Expr -> Expr
subs v@(Var name) d@(NF vt) e = case e of
    (Term vt) ->
        Term $ subs_vterm v d vt
    (LetIn mt (Left vt) e) ->
        LetIn mt (Left (subs_vterm v d vt)) (subs v d e)
    (LetIn mt (Right (fun, vts)) e) ->
        LetIn mt (Right (fun, (map (subs_vterm v d) vts))) (subs v d e)
    (DupIn mt vt e) ->
        DupIn mt (subs_vterm v d vt) (subs v d e)
    (Match vt cs) ->
        Match (subs_vterm v d vt) (map (subs_case v d) cs)
    (MatEq (vt1, vt2) c1 c2) ->
        MatEq (subs_vterm v d vt1, subs_vterm v d vt2) (subs_case v d c1) (subs_case v d c2)
--
subs_vterm :: Var -> Dom -> VTerm -> VTerm
subs_vterm _ _ (Lit x) = Lit x
subs_vterm v (NF vt) (Atom v') = if v == v' then vt else Atom v'
subs_vterm v d (Prod vt1 vt2) = Prod (subs_vterm v d vt1) (subs_vterm v d vt2)
subs_vterm v d (Fst vt) = Fst $ subs_vterm v d vt
subs_vterm v d (Snd vt) = Snd $ subs_vterm v d vt
--
subs_case :: Var -> Dom -> Case -> Case
subs_case v d (mt :--> e) = mt :--> (subs v d e)
--
