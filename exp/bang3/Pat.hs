module Pat where
--
import Expr
import Env
import Func
--
import Data.Maybe (fromMaybe)
--
matching :: Val -> [Case] -> (Env, Expr)
-- robustness of matchables
matching v (Atom ma :~> e : _) =
    (update Linear mempty (Atom ma) v, e)
-- for pair
matching (Pair v1 v2) (Prod mt1 mt2 :~> e : _) =
    let env1 = update Linear mempty mt1 v1
        env2 = update Linear env1 mt2 v2
    in (env2, e)
-- for literal value
matching (N nat) (Lit (N n) :~> e : cs)
    | nat == n = (mempty, e)
    | otherwise = matching (N nat) cs
matching (B b) (Lit (B b') :~> e : cs)
    | b == b' = (mempty, e)
    | otherwise = matching (B b) cs
-- for de-Succ
matching (N (S nat))  (NatS mt :~> e : cs) =
    fromMaybe (matching (N (S nat)) cs) $
        localMatchingN (N nat) (mt :~> e)
-- error and skip
matching (Closure _ _) _ = error $
    "<<matching | Illegal value >>\n"++
    "\tFunction cannot be matched"
matching val (_ : cs) = matching val cs
matching val [] = error $
    "<<matching | Cases exhausted>>\n"++
    "\tNon-exhaustive patterns for: " ++ show val

-- locally matching over Nat
localMatchingN :: Val -> Case -> Maybe (Env, Expr)
localMatchingN vNat (Atom (Mat ma) :~> e)
    = Just ((Var ma, vNat) `consL` mempty, e)
localMatchingN (N n) (Lit (N m) :~> e)
    = if n == m then Just (mempty, e) else Nothing
localMatchingN (N (S nat)) (NatS mt :~> e)
    = localMatchingN (N nat) (mt :~> e)
localMatchingN _ _ = Nothing
