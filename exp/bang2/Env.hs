module Env where
--
import Expr
--

-- take value out of linear ctx
takeout :: Env -> Var -> (Val, Env)
takeout (Env ((v2, val) : lis) nls) v1
    | v1 == v2 = (val, Env lis nls)
    | otherwise =
        let (val2, Env lis' nls') = takeout (Env lis nls) v1
        in (val2, Env ((v2, val) : lis') nls')
takeout (Env [] _) v1 = error $
    "<<takeout | Environment exhausted>>\n"++
    "\tCannot find [" ++ (show v1) ++ "]."
--
-- read value from normal ctx
readout :: Env -> Var -> (Val, Env)
readout (Env lis ((v2, val) : nls)) v1
    | v1 == v2 = (val, Env lis ((v2, val) : nls))
    | otherwise =
        let (val2, Env lis' nls') = readout (Env lis nls) v1
        in (val2, Env lis' ((v2, val) : nls'))
readout (Env [] _) v1 = error $
    "<<readout | Environment exhausted>>\n"++
    "\tCannot find [" ++ (show v1) ++ "]."
--

-- read variable out of linear ctx
reveal :: Env -> VTerm -> (Val, Env)
reveal env (Lit val) = (val, env)
reveal env (Atom va) = takeout env va
reveal env (Prod vt1 vt2) =
    let (val1, env1) = reveal env vt1
        (val2, env2) = reveal env1 vt2
    in (Pair val1 val2, env2)
reveal env (NatS vt) =
    let (N nat, env1) = reveal env vt
    in (N $ S nat, env1)
--
revealMore :: Env -> [VTerm] -> [Val] -> ([Val], Env)
revealMore env [] vs = (reverse vs, env)
revealMore env (vt : vts) vs =
    let (val, env') = reveal env vt
    in revealMore env' vts (val : vs)

-- write variable into linear ctx
update :: Env -> MTerm -> Val -> Env
update env (NatS mt)          (N (S nat)) = update env mt (N nat)
update env (Prod mt1 mt2)    (Pair v1 v2) = update (update env mt1 v1) mt2 v2
update env (Atom (Mat name))          val = (Var name, val) `consL` env
update env (Lit _)                      _ = env
update env mt v = error $
    "<<update | Unknown>>\n"++
    "\n\tMT{"++(show mt)++"}"++
    "\n\tVal{"++(show v)++"}"++
    "\n\tEnv{"++(show env)++"}"
--
updatec :: Env -> (MTerm, Val) -> Env
updatec e (m, v) = update e m v
--

-- read variable out of linear ctx
peek :: Env -> VTerm -> (Val, Env)
peek env (Lit val) = (val, env)
peek env (Atom va) = readout env va
peek env (Prod vt1 vt2) =
    let (val1, env1) = peek env vt1
        (val2, env2) = peek env1 vt2
    in (Pair val1 val2, env2)
peek env (NatS vt) =
    let (N nat, env1) = peek env vt
    in (N $ S nat, env1)

-- write variable into linear ctx
write :: Env -> MTerm -> Val -> Env
write env (NatS mt)          (N (S nat)) = write env mt (N nat)
write env (Prod mt1 mt2)    (Pair v1 v2) = write (write env mt1 v1) mt2 v2
write env (Atom (Mat name))          val = (Var name, val) `consN` env
write env (Lit _)                      _ = env
write env mt v = error $
    "<<write | Unknown>>\n"++
    "\n\tMT{"++(show mt)++"}"++
    "\n\tVal{"++(show v)++"}"++
    "\n\tEnv{"++(show env)++"}"

--
