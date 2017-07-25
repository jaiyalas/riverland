module Typing where
--
import Expr
import Free
--
import Data.List (find)
import Data.Maybe (fromJust)
import Data.Bifunctor
import Control.Monad.Reader
--
import Debug.Trace
--
typeof0 :: Term -> Compt Typ
--
typeof0 (Lit v) = return $ fromJust $ typeofVal v
typeof0 (Succ t) = (\TNat -> TNat) <$> (typeof0 t)
--
{-
     ---------------  intuitionistic-ID
     [x : A] ⊢ x : A
-}
-- typeof0 (BVar name) = asks (fromJust . peekByKey name . fst)
typeof0 (BVar name) = do
    (ns, ls) <- ask
    if ls == []
        then return $ fromJust $ peekByKey name ns
        else error $ "something leftover (BVar)" ++ (show ls)
--
{-
     ---------------  linear-Id
     <x : A> ⊢ x : A
-}
-- typeof0 (Var  name) = asks (fromJust . peekByKey name . snd)
typeof0 (Var  name) = do
    (_, ls) <- ask
    let (maybev, lsLeft) = popByKey name ls
    if lsLeft == []
        then return $ fromJust maybev
        else error $ "something leftover (Var) " ++ (show lsLeft)
--
{-
     Γ ⊢ t1 : A    Δ ⊢ t2 : B
    ---------------------------  ⊗-I
     Γ,Δ ⊢ (t1, t2) : A ⊗ B
-}
typeof0 (Pair t1 t2) = do
    (ns, ls) <- ask
    let (lsT1, lsT2) = splitEnvWithTerm t1 ls
    ty1 <- local (const (ns, lsT1)) (typeof0 t1)
    ty2 <- local (const (ns, lsT2)) (typeof0 t2)
    return (TProd ty1 ty2)
--
{-
     Γ,<x : A> ⊢ t : B
    --------------------  ⊸-I
     Γ ⊢ λ x t : A ⊸ B
-}
typeof0 (Abs name inTyp fbody outTyp) =
    return $ TFun inTyp outTyp
--
{-
     Γ ⊢ f : A ⊸ B    Δ ⊢ t : A
    -----------------------------  ⊸-E
     Γ,Δ ⊢ f t : B
-}
typeof0 (App (func, arg)) = do
    (ns, ls) <- ask
    let (lsArg, lsFun) = splitEnvWithTerm arg ls
    argTy <- local (const (ns, lsArg)) (typeof0 arg)
    (TFun inTy outTy) <- local (const (ns, lsFun)) (typeof0 func)
    if inTy == argTy
        then return outTy
        else error "mismatch(app)"
--
typeof0 (AppIn (Var name) (func, arg) next) = do
    (ns, ls) <- ask
    let (lsArg, lsLeft) = splitEnvWithTerm arg ls
    let (lsFun, lsNext) = splitEnvWithTerm func lsLeft
    (TFun inTy outTy) <- local (const (ns, lsFun)) (typeof0 func)
    argT <- local (const (ns, lsArg)) (typeof0 arg)
    if argT == inTy
        then local (const (ns, (name, outTy) : lsNext)) (typeof0 next)
        else error "mismatch(appin)"
--
{-
     Γ ⊢ t : A ⊗ B    Δ,<x : A>,<y : B> ⊢ e : C
    ----------------------------------------------  ⊗-E
     Γ, Δ ⊢ case t of (x,y) → e : C
-}
typeof0 (LetIn (Pair (Var name1) (Var name2)) t next) = do
    (ns, ls) <- ask
    let (ls4t, ls4next) = splitEnvWithTerm t ls
    (TProd t1 t2) <- local (const (ns, ls4t)) (typeof0 t)
    let newEnv = consL (name2, t2) $ consL (name1, t1) (ns, ls4next)
    local (const newEnv) (typeof0 next)
--
{-
     Γ ⊢ t : A    Δ,<x : A> ⊢ e : B
    --------------------------------
     Γ,Δ ⊢ let x = t in e : B
-}
typeof0 (LetIn (Var name) t next) = do
    (ns, ls) <- ask
    let (ls4t, ls4next) = splitEnvWithTerm t ls
    tt <- local (const (ns, ls4t)) (typeof0 t)
    let newEnv = consL (name, tt) (ns, ls4next)
    local (const newEnv) (typeof0 next)
--
{-
    [Γ] ⊢ t : A
    ---------------  !-I
    [Γ1] ⊢ !t : !A
        ⋅
        ⋅
        ⋅
    Γ ⊢ t : A            Δ,[!x : A] ⊢ e : B
    ------------------------------------------
    Γ,Δ ⊢ let !x = t in e : B
-}
typeof0 (BanIn (BVar name) t next) = do
    (ns, ls) <- ask
    let (ls4t, ls4next) = splitEnvWithTerm t ls
    tt <- local (const (ns, ls4t)) (typeof0 t)
    let newEnv = consN (name, tt) (ns, ls4next)
    local (const newEnv) (typeof0 next)
--
typeof0 (RecIn (BVar name) t next) = do
    (ns, ls) <- ask
    let (ls4t, ls4next) = splitEnvWithTerm t ls
    tt@(TFun inTy outTy) <- local (const (ns, ls4t)) (typeof0 t)
    let newEnv = consN (name, tt) (ns, ls4next)
    local (const newEnv) (typeof0 next)
--
{-
    Γ ⊢ t : A    Δ,<x : A, y : A> ⊢ e : B
    -------------------------------------
    Γ,Δ ⊢ let (x, y) = (t, t) in e : B
-}
typeof0 (DupIn (Pair (Var name1) (Var name2)) t next) = do
    (ns,ls) <- ask
    let (ls4t, ls4next) = splitEnvWithTerm t ls
    tt <- local (const (ns, ls4t)) (typeof0 t)
    let newEnv = consL (name2, tt) $ consL (name1, tt) (ns, ls4next)
    local (const newEnv) (typeof0 next)
--
{-
    Γ ⊢ t : A    Δ,<p1 : A> ⊢ t1 : B    ...    Δ,<pn : A> ⊢ tn : B
    ---------------------------------------------------------------
    Γ,Δ ⊢ match t of {p1 → t1; ...; pn → tn} : B
-}
typeof0 (Match t cases) = do
    (ns, ls) <- ask
    let (lsLeft, lst) = splitEnvWithTerm t ls
    tt <- local (const (ns, lst)) (typeof0 t)
    ts <- mapM (matTAll (ns, lsLeft) tt) cases
    if (allSame ts)
        then return (head ts)
        else error "mismatch"
--
{-

    --------------------

-}
typeof0 (MatEq t caseEq caseNEq) = do
    (ns, ls) <- ask
    let (lsLeft, lst) = splitEnvWithTerm t ls
    tt <- local (const (ns, lst)) (typeof0 t)
    case tt of
        (TProd t1 t2) -> if t1 == t2
            then matTAll (ns, lsLeft) t1 caseEq
            else matTAll (ns, lsLeft) t2 caseNEq
        otherwise -> error "mismatchEq"
--





--
matTAll :: DualEnv Typ -> Typ -> Case -> Compt Typ
matTAll (ns,ls) t (e :~> next) = do
    let (nsNext, lsNext) = fromJust $ matchingT t e
        newEnv = traceShowId $ (ns +>+ nsNext, ls +>+ lsNext)
    local (const newEnv) (typeof next)
--
matchingT :: Typ -> Term -> Maybe (DualEnv Typ)
matchingT t (Var vname)  = return $ (vname, t) `consL` mempty
matchingT t (BVar vname) = return $ (vname, t) `consN` mempty
matchingT TNat  (Lit (N _)) = return mempty
matchingT t     (Lit (N _)) = Nothing
matchingT TBool (Lit (B _)) = return mempty
matchingT t     (Lit (B _)) = Nothing
matchingT TNat  (Succ e) = matchingT TNat e
matchingT (TProd t1 t2) (Pair e1 e2) = do
    env1 <- matchingT t1 e1
    env2 <- matchingT t2 e2
    return $ env1 `mappend` env2
matchingT t e = Nothing
--
typeofVal :: Val -> Maybe Typ
typeofVal (B _) = return TBool
typeofVal (N _) = return TNat
typeofVal (Pr v1 v2) = do
    x <- typeofVal v1
    y <- typeofVal v2
    return $ TProd x y
typeofVal v = Nothing
--
allSame :: Eq a => [a] -> Bool
allSame [ ] = True
allSame [ a ] = True
allSame (a : b : xs) = a == b && allSame (b : xs)
--
typeof1 :: Term -> (Compt Typ -> Compt Typ) -> Compt Typ
typeof1 = undefined
--
typeof = typeof0
