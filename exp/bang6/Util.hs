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
lookupCtx' :: CtxSwitch
           -> Ctx VName a
           -> VName
           -> Except ErrorMsg a
lookupCtx' sw ctx x =
    case lookupCtx sw ctx x of
        Just v -> return v
        Nothing -> throwError $ NotFound $ CtxExhausted sw x
--
-- popCtx :: (Eq k, Show k)
--        => CtxSwitch
--        -> Ctx k v
--        -> k
--        -> Maybe (v, Ctx k v)
popCtx' :: CtxSwitch -> Ctx VName v -> VName
        -> Except ErrorMsg  (v, Ctx VName v)
popCtx' sw ctx vn =
    case popCtx sw ctx vn of
        Just x -> return x
        Nothing -> throwError $ NotFound $ CtxExhausted sw vn

deVar :: Expr -> Except ErrorMsg (VName, CtxSwitch)
deVar (Var n) = return (n, Linear)
deVar (BVar n) = return (n, Normal)
deVar e = throwError $ MismatchSynt $ NotAVariable e
--
splitCtxExpr :: Eq v => Expr -> Ctx VName v -> Except ErrorMsg (Ctx VName v, Ctx VName v)
splitCtxExpr e ctx =
    let (fvsl, fvsn) = (freeVar e)
    in withExcept foo $ splitCtx fvsl ctx
--
foo :: CtxInternalError VName -> ErrorMsg
foo (CtxError k) = NotFound $ CtxSplitError k
