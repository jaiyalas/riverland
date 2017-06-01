module Eval where
--
import Types
import Expr
import Error
import Ctx
import Util
--
import Control.Monad.Except
import Control.Monad.Reader
--
-- type Check a = ExceptT ErrorMsg (Reader (Ctx VName a)) a
--
eval :: Expr -> Check Val
eval (Lit v) = return v
eval (Var vname) = do
    ctx <- ask
    runExceptId $ lookupCtx' Linear ctx vname
eval (BVar vname) = do
    ctx <- ask
    runExceptId $ lookupCtx' Normal ctx vname
eval (Suc e) = do
    v <- eval e
    case v of
        (N n) -> return (N (S n))
        otherwise ->
            throwError $
            MismatchSynt $
            InvalidConstructor (Suc e)
eval (Pair e1 e2) = do
    -- HERE !!! HERE !!! HERE !!!
    -- HERE !!! HERE !!! HERE !!!
    -- HERE !!! HERE !!! HERE !!!
    v1 <- eval e1
    v2 <- eval e2
    return (Pr v1 v2)
-- Lambda 的 parameter 限定是 linear (所以只能給 VName)
eval fun@(Lam _ _ _ _) = do
    ctx <- ask
    return (Closure ctx fun)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
eval (LetIn (Pair e1 e2) e next) = do
    v <- eval e
    case v of
        (Pr v1 v2) -> do
            -- HERE !!! HERE !!! HERE !!!
            -- HERE !!! HERE !!! HERE !!!
            -- HERE !!! HERE !!! HERE !!!
            eval (LetIn e1 (Lit v1) $ LetIn e2 (Lit v2) $ next)
        otherwise -> throwError $ MismatchSynt $ NotAPair e
eval (LetIn (Var name) e next) = do
    v <- eval e
    local (insertL name v) (eval next)
eval (RecIn (BVar name) e next) = do
    v <- eval e
    case v of
        fun@(Closure fenv fbody) -> do
            let funR = Closure (insertN name funR fenv) fbody
            local (insertN name funR) (eval next)
        otherwise ->
            throwError $ MismatchSynt $ NotAFunction e
eval (BanIn (BVar vname) e next) = do
    v <- eval e
    local (insertL vname v) (eval next)
eval (DupIn (Pair (Var vn1) (Var vn2)) e next) = do
    v <- eval e
    local (insertL vn2 v . insertL vn1 v) (eval next)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- 可以接受 lambda 來做為 application 的格式
-- Lambda 的 parameter 限定是 linear (所以只能給 VName)
eval (AppIn (Var resName) (Lam fmt tyIn fbody tyOut, _arg) next) = do
    ctx <- ask
    (arg, swArg) <- runExceptId $ deVar _arg
    argV <- runExceptId $ lookupCtx' swArg ctx arg
    -- HERE !!! HERE !!! HERE !!!
    -- HERE !!! HERE !!! HERE !!!
    -- HERE !!! HERE !!! HERE !!!
    resV <- local (insertL fmt argV) (eval fbody)
    local (insertL resName resV) (eval next)
-- 可以接受 (Var/BVar fun) (Var/BVar arg) 共四種 application modes
eval (AppIn (Var resName) (_fun, _arg) next) = do
    ctx <- ask
    (fun, swFun) <- runExceptId $ deVar _fun
    (arg, swArg) <- runExceptId $ deVar _arg
    v1 <- runExceptId $ lookupCtx' swFun ctx fun
    case v1 of
        (Closure fenv (Lam fmt tyIn fbody tyOut)) -> do
            argV <- runExceptId $ lookupCtx' swArg ctx arg
            -- HERE !!! HERE !!! HERE !!!
            -- HERE !!! HERE !!! HERE !!!
            -- HERE !!! HERE !!! HERE !!!
            resV <- runCheckWith (insertL fmt argV fenv) (eval fbody)
            local (insertL resName resV) (eval next)
        otherwise -> throwError $ MismatchSynt $ NotAFunction _fun
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
eval (Match e cases) = do
    v <- eval e
    (newEnv, next) <- runExceptId $ findMatched v cases
    local (mappend newEnv) (eval next)
eval (MatEq e caseEq caseNEq) = do
    v <- eval e
    case v of
        (Pr v1 v2) -> if v1 == v2
            then eval $ Match (Lit v1) [caseEq]
            else eval $ Match (Pair (Lit v1) (Lit v2)) [caseEq]
        otherwise -> throwError $ MismatchSynt $ NotAPair e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
eval e = throwError $ MismatchSynt $ UnknownSyntaxError e
--
--



matching :: Val -> Expr -> Except ErrorMsg (Ctx VName Val)
matching v (Var vname) =
    return $ insertL vname v mempty
matching v (BVar vname) =
    return $ insertN vname v mempty
matching (N n1) (Lit (N n2)) = if n1 == n2
    then return mempty
    else throwError $ MismatchPatt $ Simple (N n1) (Lit (N n2))
matching (B b1) (Lit (B b2)) = if b1 == b2
    then return mempty
    else throwError $ MismatchPatt $ Simple (B b1) (Lit (B b2))
matching (N (S n1)) (Suc e) = matching (N n1) e
matching (Pr v1 v2) (Pair e1 e2) = do
    env1 <- matching v1 e1
    env2 <- matching v2 e2
    return $ env1 `mappend` env2
matching v e = throwError $ MismatchPatt $ Illegal v e
--
findMatched :: Val -> [Case] -> Except ErrorMsg (Ctx VName Val, Expr)
-- findMatched v (mat :~> next : cs) = do
--     { ctx <- matching v mat
--     ; return (ctx, next)
--     } `catchError` (\_ -> findMatched v cs)
findMatched v (mat :~> next : cs) =
    (matching v mat >>= (\ctx -> return (ctx, next)))
    `catchError` (\_ -> findMatched v cs)
findMatched v [] =
    throwError $ MismatchPatt $ Exhausted
