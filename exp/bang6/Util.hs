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
runCheckWith :: (Ctx VName a) -> Check a -> Check a
runCheckWith = runExceptReaderWith
--
lookupCtx' :: CtxSwitch
           -> Ctx VName a
           -> VName
           -> Except ErrorMsg a
lookupCtx' sw ctx x =
    case lookupCtx sw ctx x of
        Just v -> return v
        Nothing -> throwError $ NotFound $ CtxExhausted sw x
--
deVar :: Expr -> Except ErrorMsg (VName, CtxSwitch)
deVar (Var n) = return (n, Linear)
deVar (BVar n) = return (n, Normal)
deVar e = throwError $ MismatchSynt $ NotAVariable e
