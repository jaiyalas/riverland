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

--
