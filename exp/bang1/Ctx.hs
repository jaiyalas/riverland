module Ctx where
--
import Expr
--
find :: Env -> Var -> (Val, Env)
find ((v2, val) : env) v1
    | v1 == v2 = (val, env)
    | otherwise = let (val2, env2) = find env v1
        in (val2, (v2, val) : env2)
find [] v1 = error $ "Cannot find [" ++ (show v1) ++ "]"
--
{- reveal value from environment -}
--
revealVT :: Env -> VTerm -> (Val, Env)
revealVT env (Lit val) = (val, env)
revealVT env (Atom va) = find env va
revealVT env (Prod vt1 vt2) =
    let (val1, env1) = revealVT env vt1
        (val2, env2) = revealVT env1 vt2
    in (Pair val1 val2, env2)
revealVT env (NatS vt) =
    let (N nat, env1) = revealVT env vt
    in (N $ S nat, env1)
--
revealVTs :: Env -> [VTerm] -> [Val] -> ([Val], Env)
revealVTs env [] vs = (reverse vs, env)
revealVTs env (vt : vts) vs =
    let (val, env') = revealVT env vt
    in revealVTs env' vts (val : vs)
--
{- update value from environment -}
--
updateMT :: Env -> MTerm -> Val -> Env
updateMT env (NatS mt)
             (N (S nat))
             = updateMT env mt (N nat)
updateMT env (Prod mt1 mt2)
             (Pair v1 v2)
             = updateMT (updateMT env mt1 v1) mt2 v2
updateMT env (Atom (Mat name))
             val
             = (Var name, val) : env
updateMT env (Lit _) _ = env
updateMT env mt v = error $
    "\n\tMT{"++(show mt)++"}"++
    "\n\tVal{"++(show v)++"}"++
    "\n\tEnv{"++(show env)++"}"
--
updateMTc :: Env -> (MTerm, Val) -> Env
updateMTc e (m, v) = updateMT e m v
--

--
