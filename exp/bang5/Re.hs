-- {-# LANGUAGE ExistentialQuantification #-}
-- {-# LANGUAGE RankNTypes #-}
-- {-# LANGUAGE StandaloneDeriving #-}
-- {-# LANGUAGE FlexibleInstances #-}
module Re where
--
import Data.List
import Data.Bifunctor
import Control.Monad.Reader
import Debug.Trace
--

type Name = String

data Type = TInt | T1 | T2
          | TFun Type Type
          deriving Show
data Expr = Var Name
          | Lit Int
          | Lam Name Type Expr
          | App Expr Expr
          deriving Show

type Env = [(Name, Type)]

type Check = Reader Env

extend :: (Name, Type) -> Env -> Env
extend xt env = xt : env

inEnv :: (Name, Type) -> Check a -> Check a
inEnv (x,t) = local (extend (x,t))

lookupVar :: Name -> Check Type
lookupVar x = do
  env <- ask
  case lookup x env of
    Just e  -> return e
    Nothing -> error "..."

check :: Expr -> Check Type
check (Var name) = lookupVar name
check (Lit _) = return TInt
check (Lam name ty e) = do
    env <- inEnv (name,ty) $ check e
    traceShow env $ return $ TFun ty env
check (App e1 e2) = undefined
