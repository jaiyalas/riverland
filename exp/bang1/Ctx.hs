module Ctx where
--
import Expr
--
type Env = [(Var, Val)]
--
find :: Var -> Env -> (Val, Env)
find va [] = error $ "there is no such variable" ++ (show va)
find v1 ((v2, val) : env)
    | v1 == v2 = (val, env)
    | otherwise = let (val2, env2) = find v1 env
        in (val2, (v2, val) : env2)
--
appSigma :: Env -> VTerm -> (Val, Env)
appSigma env (Lit val) = (val, env)
appSigma env (Atom va) = find va env
appSigma env (Prod vt1 vt2) =
    let (val1, env1) = appSigma env vt1
        (val2, env2) = appSigma env1 vt2
    in (Pair val1 val2, env2)
appSigma env (NatS vt) =
    let (N nat, env1) = appSigma env vt
    in (N $ S nat, env1)
--
appSigmaList :: Env -> [VTerm] -> [Val] -> ([Val], Env)
appSigmaList env [] vs = (reverse vs, env)
appSigmaList env (vt : vts) vs =
    let (val, env') = appSigma env vt
    in appSigmaList env' vts (val : vs)
--
zipMatEnv :: MTerm -> Val -> Env -> Env
zipMatEnv (NatS mt) (N (S nat)) env = zipMatEnv mt (N nat) env
zipMatEnv (Prod mt1 mt2) (Pair v1 v2) env =
    zipMatEnv mt2 v2 $ zipMatEnv mt1 v1 $ env
-- zipMatEnv (Atom (Mat name)) (N n) env = (Var name, N n) : env
-- zipMatEnv (Atom (Mat name)) (B b) env = (Var name, B b) : env
-- zipMatEnv (Atom (Mat name)) (Pair v1 v2) env = (Var name, Pair v1 v2) : env
-- these three are identical, merged as follow
zipMatEnv (Atom (Mat name)) v env = (Var name, v) : env
zipMatEnv mt v env = error $ "\n\tMT{"++(show mt)++"} \n\tVal{"++(show v)++"} \n\tEnv{"++(show env)++"}"
--
zipMatEnvC :: (MTerm, Val) -> Env -> Env
zipMatEnvC (m, v) e = zipMatEnv m v e
--

--
