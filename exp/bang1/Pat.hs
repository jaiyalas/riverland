module Pat where
--
import Expr
import Func
import Ctx
--
import Data.Maybe (fromMaybe)
--

matching :: Val -> [Case] -> (Env, Expr)
-- robustness of matchable
matching v      ((Atom ma :~> e) : _) =
    (updateMT [] (Atom ma) v, e)
-- matching to pair
matching (Pair v1 v2) ((Prod mt1 mt2 :~> e) : _) =
    let env1 = updateMT [] mt1 v1
        env2 = updateMT env1 mt2 v2
    in (env2, e)
--
matching (N nat)      ((Lit (N n) :~> e) : cs)
    | nat == n = ([], e)
    | otherwise = matching (N nat) cs
matching (B b)        ((Lit (B b') :~> e) : cs)
    | b == b' = ([], e)
    | otherwise = matching (B b) cs
--
{- todo: unifying above two cases -}
--
matching (N (S nat))  ((NatS mt :~> e) : cs) =
    fromMaybe (matching (N (S nat)) cs) $ localMatchingN (N nat) (mt :~> e)
-- error and skip
matching (Closure _ _) _ = error $ "Function cannot be matched"
matching val (_ : cs) = matching val cs
matching val [] = error $ "Non-exhaustive patterns for: " ++ show val


-- locally matching over Nat
localMatchingN :: Val -> Case -> Maybe (Env, Expr)
localMatchingN vNat (Atom (Mat ma) :~> e)
    = Just ([(Var ma, vNat)], e)
localMatchingN (N n) (Lit (N m) :~> e)
    = if n == m then Just ([], e) else Nothing
localMatchingN (N (S nat)) (NatS mt :~> e)
    = localMatchingN (N nat) (mt :~> e)
localMatchingN _ _ = Nothing
