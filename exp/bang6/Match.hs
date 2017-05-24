module Match where
--
import Types
import Expr
import Ctx
--
import Data.Maybe (fromMaybe)
import Control.Monad.Except
--




-- data Val     = N Nat
--              | B Bool
--              | Pr Val Val
--              | Closure (Ctx VName Val) Expr
--

matching :: Val -> Expr -> Except MatError (Ctx VName Val)
matching v (Var vname) =
    return (insertCtx fst L (vname, v) mempty)
matching (N n1) (Lit (N n2)) = if n1 == n2
        then return mempty
        else throwError Mismatch
matching (N (S n1)) (Suc e) = matching (N n1) e
matching (B b1) (Lit (B b2)) = if b1 == b2
    then return mempty
    else throwError Mismatch
matching (Pr v1 v2) (Pair e1 e2) = do
    env1 <- matching v1 e1
    env2 <- matching v2 e2
    return $ env1 `mappend` env2
matching (Closure _ _) _ = throwError MatClosure
matching _ _ = throwError IllMatch






matchings :: Val -> [Case] -> Except MatError (Ctx VName Val, Expr)
matchings v (mat :~> next : cs) =




    return (insertCtx fst L (vname, v) mempty, next)
--
matchings (N n1) (Lit (N n2) :~> next : cs) =
    if n1 == n2
        then return (mempty, next)
        else throwError MismatchNat -- matching (N n1) cs
matchings (N (S n))       (Suc e :~> next : cs) =
    () `catchError`
    return (mempty, next)





--
matching (B nat)     (pat :~> next : cs) = undefined
-- -- Pair Expr Expr
matching (Pr v1 v2)  (Pair e1 e2 :~> next : cs) = undefined
    -- matching v1 e1
    -- let env1 = insert Linear mt1 v1 mempty
    --     env2 = insert Linear mt2 v2 env1
    -- in return (env2, e)
--
matching (Closure ctx expr) (pat :~> next : cs) = undefined
matching val (_ : cs) = matching val cs
matching val [] =
    throwError $ MatCtxExhausted
