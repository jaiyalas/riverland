module Match where
--
import Expr
import Env
--
import Data.Maybe (fromMaybe)
--
-- matching a new env and its (next) togo expr
matching :: Val -> [Case] -> (Env, Expr)
matching v (Atom ma :~> e : _) = (insert Linear mempty (Atom ma) v, e)
matching (Pr v1 v2) (Prod mt1 mt2 :~> e : _) =
    let env1 = insert Linear mempty mt1 v1
        env2 = insert Linear env1   mt2 v2
    in (env2, e)
matching (N nat) (Lit (N n) :~> e : cs)
    | nat == n = (mempty, e)
    | otherwise = matching (N nat) cs
-- alternative maching over nat
matching (N Z) (NatZ :~> e : cs) = (mempty, e)
-- locallyNatMatching is required because of
-- the mt could beany one of Atom/NatS/Lit Nat.
-- this sould be able to avoid by adding types
matching (N (S nat)) (NatS mt :~> e : cs) =
    fromMaybe (matching (N (S nat)) cs) $
        locallyNatMatching (N nat) (mt :~> e)
matching (B b) (Lit (B b') :~> e : cs)
    | b == b' = (mempty, e)
    | otherwise = matching (B b) cs
-- error and skip
matching val (_ : cs) = matching val cs
matching (Closure _ _) _ = error $
    "<< matching | Illegal value >>\n"++
    "\tFunction cannot be matched"
matching val [] = error $
    "<< matching | Cases exhausted >>\n"++
    "\tNon-exhaustive patterns for: " ++ show val
--
-- locally matching over Nat
locallyNatMatching :: Val -> Case -> Maybe (Env, Expr)
locallyNatMatching vNat (Atom (Mat ma) :~> e)
    = Just ((Var ma, vNat) `consL` mempty, e)
locallyNatMatching (N n) (Lit (N m) :~> e)
    = if n == m then Just (mempty, e) else Nothing
locallyNatMatching (N (S nat)) (NatS mt :~> e)
    = locallyNatMatching (N nat) (mt :~> e)
locallyNatMatching _ _ = Nothing
