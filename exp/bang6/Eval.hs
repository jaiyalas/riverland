module Eval where
--
import Types
import Expr
import Error
import Ctx
import Match
--
import Control.Monad.Except
import Control.Monad.Reader
--

type Check a = ExceptT ErrorMsg (Reader (Ctx VName a)) a

eval :: Expr -> Check Val
eval (Var vname) = do
    env <- ask
    case lookupCtx Linear env vname of
        Just v -> return v
        Nothing -> throwError $
            NotFound $ CtxExhausted Linear vname
eval (Lit v) = return v
--   | Ctr CtrName Expr
eval (Suc e) = do
    v <- eval e
    case v of
        (N n) -> return (N (S n))
        otherwise -> throwError $
            MismatchSynt $ InvalidConstructor (Suc e)
eval (Pair e1 e2) = do
    v1 <- eval e1
    v2 <- eval e2
    return (Pr v1 v2)
eval fun@(Lam  arg argT body) = do
    ctx <- ask
    return (Closure ctx fun)
-- --
eval (LetIn (Var name) localExp next) = do
    lv <- eval localExp
    local (insertCtx fst Linear (name, lv)) (eval next)
eval (RecIn (Var name) localExp outT next) = do
    lv <- eval localExp
    case lv of
        fun@(Closure fenv fbody) -> do
            ctx <- ask
            let funR = Closure (insertCtx fst Normal (name, funR) fenv) fbody
            local (insertCtx fst Normal (name, funR)) (eval next)
        otherwise -> throwError $
            MismatchSynt $ NotAFunction localExp
eval (AppIn (Var resName) (funName, arg) next) = do
    ctx <- ask
    ... lookupCtx ...
    argVal <- eval arg

-- (BanIn MTerm Expr Expr)
-- (DupIn MTerm Expr Expr)
-- --
-- (Match VTerm [Case])
-- (MatEq VTerm Case Case)
