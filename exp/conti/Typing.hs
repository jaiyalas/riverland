module Typing where
--
import Expr
--
import Data.List (find)
import Data.Maybe (fromJust)
import Data.Bifunctor
import Control.Monad.Reader
--
import Debug.Trace
--
typeof0 :: Term -> Compt Typ
typeof0 (Lit v) = return $ fromJust $ typeofVal v
typeof0 (Var  name) = asks (fromJust . peekByKey name . snd)
typeof0 (BVar name) = asks (fromJust . peekByKey name . fst)







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
