module Eval where
--
import Types
import Expr
import Error
import Ctx
import Match
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
    v1 <- eval e1
    v2 <- eval e2
    return (Pr v1 v2)
-- Lambda 的 parameter 限定是 linear (所以只能給 VName)
eval fun@(Lam _ _ _ _) = do
    ctx <- ask
    return (Closure ctx fun)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
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
