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

-- ΓΔ

typeof0 (Lit v) = return $ fromJust $ typeofVal v
typeof0 (Var  name) = asks (fromJust . peekByKey name . snd)
typeof0 (BVar name) = asks (fromJust . peekByKey name . fst)
--
typeof0 (Succ t) = (\TNat -> TNat) <$> (typeof0 t)
typeof0 (Pair t1 t2) = do
    (ns, ls) <- ask
    let (lsT1, lsT2) = splitEnvWithTerms (t1, t2) ls
    ty1 <- local (const (ns, lsT1)) (typeof0 t1)
    ty2 <- local (const (ns, lsT2)) (typeof0 t2)
    return (TProd ty1 ty2)
typeof0 (Abs name inTyp fbody outTyp) =
    return $ TFun inTyp outTy
typeof0 (App (funT, argT)) = do
    (TFun inTy outTy) <- typeof0 funT
    argTy <- typeof0 argT
    if inTy == argTy
        then return outTy
        else error "app mismatch"
--
typeof0 (LetIn (Var name) t next) = do
    tt <- typeof0 t
    local (consL (name, tt)) (typeof0 next)
typeof0 (LetIn (Pair (Var name1) (Var name2)) t next) = do
    (TProd t1 t2) <- typeof0 t
    local (consL (name2, t2) . consL (name1, t1)) (typeof0 next)
typeof0 (RecIn var t next) = undefined
typeof0 (BanIn var t next) = undefined
typeof0 (DupIn var t next) = undefined
-- AppIn MTerm (Term, Term) Term
--
typeof0 (Match var cs) = undefined
typeof0 (MatEq var caseEq caseNEq) = undefined





typeof1 :: Term -> (Compt Typ -> Compt Typ) -> Compt Typ
typeof1 = undefined






--
typeof = typeof0
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
matTAll :: Typ -> Case -> Compt Typ
matTAll t (e :~> next) = do
    let newCtx = fromJust $ matchingT t e
    -- local (mappend newCtx) (typeof next)
    local (const newCtx) (typeof next)
--
typeofVal :: Val -> Maybe Typ
typeofVal (B _) = return TBool
typeofVal (N _) = return TNat
typeofVal (Pr v1 v2) = do
    x <- typeofVal v1
    y <- typeofVal v2
    return $ TProd x y
typeofVal v = Nothing
