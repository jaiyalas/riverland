module Match where
--
import Types
import Expr
import Ctx
import Error
--
import Data.Maybe (fromMaybe)
import Control.Monad.Except
--

matching :: Val -> Expr -> Except ErrorMsg (Ctx VName Val)
matching v (Var vname) =
    return (insertCtx fst Linear (vname, v) mempty)
matching (N n1) (Lit (N n2)) = if n1 == n2
        then return mempty
        else throwError $ MismatchPatt $ Simple (N n1) (Lit (N n2))
matching (N (S n1)) (Suc e) = matching (N n1) e
matching (B b1) (Lit (B b2)) = if b1 == b2
    then return mempty
    else throwError $ MismatchPatt $ Simple (B b1) (Lit (B b2))
matching (Pr v1 v2) (Pair e1 e2) = do
    env1 <- matching v1 e1
    env2 <- matching v2 e2
    return $ env1 `mappend` env2
matching v e = throwError $ MismatchPatt $ Illegal v e

findMatched :: Val -> [Case] -> Except ErrorMsg (Ctx VName Val, Expr)
findMatched v (mat :~> next : cs) = do
    { ctx <- matching v mat
    ; return (ctx, next)
    } `catchError` (\_ -> findMatched v cs)
-- findMatched v (mat :~> next : cs) =
--     (matching v mat >>= (\ctx -> return (ctx, next)))
--     `catchError` (\_ -> findMatched v cs)
findMatched v [] =
    throwError $ MismatchPatt $ Exhausted
