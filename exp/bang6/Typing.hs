module Typing where
--
import Types
import Expr
import Error
import Ctx
import Util
--
import Control.Monad
import Control.Monad.Except
import Control.Monad.Reader
--
-- type Check a = ExceptT ErrorMsg (Reader (Ctx VName a)) a
--
typeof :: Expr -> Check Typ
typeof (Lit v) = runExceptId (typeofVal v)
typeof (Var vname) = do
    ctx <- ask
    runExceptId $ lookupCtx' Linear ctx vname
typeof (BVar vname) = do
    ctx <- ask
    runExceptId $ lookupCtx' Normal ctx vname
typeof (Suc e) = do
    t <- typeof e
    case t of
        TNat -> return TNat
        nott ->
            throwError $
            MismatchType $
            TypeError (Suc e) TNat nott
typeof (Pair e1 e2) = do
    v1 <- typeof e1
    v2 <- typeof e2
    return (TProd v1 v2)
typeof (Lam _ tyIn _ tyOut) = do
    return $ TFunc tyIn tyOut
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
typeof (LetIn (Var name) e next) = do
    v <- typeof e
    local (insertL name v) (typeof next)
typeof (RecIn (BVar name) e next) = do
    v <- typeof e
    local (insertN name v) (typeof next)
typeof (BanIn (BVar vname) e next) = do
    v <- typeof e
    local (insertL vname v) (typeof next)
typeof (DupIn (Pair (Var vn1) (Var vn2)) e next) = do
    v <- typeof e
    local (insertL vn2 v . insertL vn1 v) (typeof next)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- 可以接受 lambda 來做為 application 的格式
-- -- Lambda 的 parameter 限定是 linear (所以只能給 VName)
typeof (AppIn (Var resName) (Lam fmt tyIn fbody tyOut, _arg) next) = do
    ctx <- ask
    (arg, swArg) <- runExceptId $ deVar _arg
    argT <- runExceptId $ lookupCtx' swArg ctx arg
    if argT == tyIn
        then do
            resT <- local (insertL fmt argT) (typeof fbody)
            if resT == tyOut
                then local (insertL resName resT) (typeof next)
                else throwError $ MismatchType $ TypeError _arg resT tyOut
        else throwError $ MismatchType $ TypeError _arg argT tyIn
-- -- 可以接受 (Var/BVar fun) (Var/BVar arg) 共四種 application modes
typeof (AppIn (Var resName) (_fun, _arg) next) = do
    ctx <- ask
    (fun, swFun) <- runExceptId $ deVar _fun
    (arg, swArg) <- runExceptId $ deVar _arg
    funT <- runExceptId $ lookupCtx' swFun ctx fun
    argT <- runExceptId $ lookupCtx' swArg ctx arg
    case funT of
        (TFunc tyIn tyOut) ->
            if argT == tyIn
                then local (insertL resName tyOut) (typeof next)
                else throwError $ MismatchType $ TypeError _arg argT tyIn
        otherwise -> throwError $ MismatchType $ NotAFunctionType _fun funT
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
typeof (Match e cases) = do
    vt <- typeof e
    (t1:ts) <- mapM (matTAll vt) cases
    if (and $ map (== t1) ts)
        then return t1
        else throwError $ MismatchType $ MatchInconsist (t1:ts)
typeof (MatEq e caseEq caseNEq) = do
    vt <- typeof e
    case vt of
        (TProd t1 t2) -> if t1 == t2
            then matTAll t1 caseEq 
            else matTAll t2 caseNEq
        otherwise -> throwError $ MismatchSynt $ NotAPair e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
typeof e = throwError $ MismatchSynt $ UnknownSyntaxError e
--
--

matchingT :: Typ -> Expr -> Except ErrorMsg (Ctx VName Typ)
matchingT t (Var vname) = return $ insertL vname t mempty
matchingT t (BVar vname) = return $ insertN vname t mempty
matchingT TNat (Lit (N _)) = return mempty
matchingT t    (Lit (N _)) = throwError $ MismatchType $ TypeInconsist t TNat
matchingT TBool (Lit (B _)) = return mempty
matchingT t     (Lit (B _)) = throwError $ MismatchType $ TypeInconsist t TBool
matchingT TNat (Suc e) = matchingT TNat e
matchingT (TProd t1 t2) (Pair e1 e2) = do
    env1 <- matchingT t1 e1
    env2 <- matchingT t2 e2
    return $ env1 `mappend` env2
matchingT t e = throwError $ MismatchType $ MatchInconsist []

matTAll :: Typ -> Case -> Check Typ
matTAll t (e :~> next) = do
    newCtx <- runExceptId $ matchingT t e
    runCheckWith newCtx (typeof next)


--
typeofVal :: Val -> Except ErrorMsg Typ
typeofVal (B _) = return TBool
typeofVal (N _) = return TNat
typeofVal (Pr v1 v2) = do
    x <- typeofVal v1
    y <- typeofVal v2
    return $ TProd x y
typeofVal v = throwError $ MismatchType $ ValueTypeUnknown v
