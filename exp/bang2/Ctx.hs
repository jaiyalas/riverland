module Ctx where
--
import Expr
--
takeOut :: Env -> Var -> (Val, Env)
takeOut ((v2, val) : env) v1
    | v1 == v2 = (val, env)
    | otherwise = let (val2, env2) = takeOut env v1
        in (val2, (v2, val) : env2)
takeOut [] v1 = error $
    "<<takeOut | Environment exhausted>>\n"++
    "\tCannot find [" ++ (show v1) ++ "]."
--
reveal :: Env -> VTerm -> (Val, Env)
reveal env (Lit val) = (val, env)
reveal env (Atom va) = takeOut env va
reveal env (Prod vt1 vt2) =
    let (val1, env1) = reveal env vt1
        (val2, env2) = reveal env1 vt2
    in (Pair val1 val2, env2)
reveal env (NatS vt) =
    let (N nat, env1) = reveal env vt
    in (N $ S nat, env1)
--
reveals :: Env -> [VTerm] -> [Val] -> ([Val], Env)
reveals env [] vs = (reverse vs, env)
reveals env (vt : vts) vs =
    let (val, env') = reveal env vt
    in reveals env' vts (val : vs)
--
update :: Env -> MTerm -> Val -> Env
update env (NatS mt)
             (N (S nat))
             = update env mt (N nat)
update env (Prod mt1 mt2)
             (Pair v1 v2)
             = update (update env mt1 v1) mt2 v2
update env (Atom (Mat name))
             val
             = (Var name, val) : env
update env (Lit _) _ = env
update env mt v = error $
    "<<update | Unknown>>\n"++
    "\n\tMT{"++(show mt)++"}"++
    "\n\tVal{"++(show v)++"}"++
    "\n\tEnv{"++(show env)++"}"
--
updatec :: Env -> (MTerm, Val) -> Env
updatec e (m, v) = update e m v
--

--
