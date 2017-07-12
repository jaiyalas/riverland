module Util where
--
import Expr
import Ctx
import Error
--
import Control.Monad.Except
import Control.Monad.Reader
--
import Data.Functor.Identity
--
type Check a = ExceptT ErrorMsg (Reader (Ctx VName a)) a
--
runExceptId :: Monad n => ExceptT e Identity a -> ExceptT e n a
runExceptId = mapExceptT (return . runIdentity)
--
runExceptReaderWith :: Ctx VName a -> Check a -> Check a
runExceptReaderWith ctx = mapExceptT (return . (flip runReader) ctx)
--
runCheckWith :: Ctx VName v -> Check v -> Check v
runCheckWith = runExceptReaderWith
--


deVar :: Expr -> Except ErrorMsg (VName, CtxSwitch)
deVar (Var n) = return (n, Linear)
deVar (BVar n) = return (n, Normal)
deVar e = throwError $ MismatchSynt $ NotAVariable e

splitCtxExpr' :: (Monad n, Eq v)
              => Expr
              -> Ctx VName v
              -> ExceptT ErrorMsg n (Ctx VName v, Ctx VName v)
splitCtxExpr' e = runExceptId . splitCtxExpr e

splitCtxExpr :: Eq v => Expr -> Ctx VName v -> Except ErrorMsg (Ctx VName v, Ctx VName v)
splitCtxExpr e ctx =
    let (fvsl, fvsn) = (freeVar e)
    in withExcept foo $ splitCtx fvsl ctx
--
foo :: CtxInternalError VName -> ErrorMsg
foo (CtxError k) = NotFound $ CtxSplitError k
