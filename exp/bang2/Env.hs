module Env where
--
import Expr
--
type Ctx = [(Var, Val)]
data Env = Env Ctx Ctx deriving (Show, Eq)
data CtxSwitch = Normal | Linear deriving (Show, Eq)

{-- ###################################

    Environment / Context accessors

################################### --}

-- name based random access(?)
raccess :: CtxSwitch -> Env -> Var -> (Val, Env)
raccess Normal (Env lis ((v2, val) : nls)) v1
    | v1 == v2 = (val, Env lis ((v2, val) : nls))
    | otherwise =
        let (val2, Env lis' nls') = raccess Normal (Env lis nls) v1
        in (val2, Env lis' ((v2, val) : nls'))
raccess Normal (Env _ []) v1 = error $
    "<<takeout | Environment exhausted>>\n"++
    "\tCannot find \"" ++ (show v1) ++ "\" in normal context."
raccess Linear (Env ((v2, val) : lis) nls) v1
    | v1 == v2 = (val, Env lis nls)
    | otherwise =
        let (val2, Env lis' nls') = raccess Linear (Env lis nls) v1
        in (val2, Env ((v2, val) : lis') nls')
raccess Linear (Env [] _) v1 = error $
    "<<takeout | Environment exhausted>>\n"++
    "\tCannot find \"" ++ (show v1) ++ "\" in linear context."
--

-- structural-variable based random access(?)
reveal :: CtxSwitch -> Env -> VTerm -> (Val, Env)
reveal _ env (Lit val) = (val, env)
reveal ctxSW env (Atom va) = raccess ctxSW env va
reveal ctxSW env (Prod vt1 vt2) =
    let (val1, env1) = reveal ctxSW env vt1
        (val2, env2) = reveal ctxSW env1 vt2
    in (Pair val1 val2, env2)
reveal ctxSW env (NatS vt) =
    let (N nat, env1) = reveal ctxSW env vt
    in (N $ S nat, env1)
--

-- structural-matchable based random access(?)
update :: CtxSwitch -> Env -> MTerm -> Val -> Env
update _ env (Lit _) _ = env -- value is unwritable
update Normal env (Atom (Mat name)) val = (Var name, val) `consN` env
update Linear env (Atom (Mat name)) val = (Var name, val) `consL` env
update ctxSW env (NatS mt) (N (S nat)) = update ctxSW env mt (N nat)
update ctxSW env (Prod mt1 mt2) (Pair v1 v2) =
    update ctxSW (update ctxSW env mt1 v1) mt2 v2
update ctxSW env mt v = error $
    "<<update | Unknown>>\n"++
    "\tCannot update \"" ++ (show mt) ++ "/" ++ (show v) ++
    "\" in "++(show ctxSW)++" context."


{-- ###################################

    Environment / Context operations

################################### --}
(+>+) :: Eq a => [(a,b)] -> [(a,b)] -> [(a,b)]
((k,v):xs) +>+ ys
    | elem k (map fst ys) = (k,v) : xs +>+ (filter ((/= k).fst) ys)
    | otherwise = (k,v) : xs +>+ ys
[] +>+ ys = ys

(+<+) :: Eq a => [(a,b)] -> [(a,b)] -> [(a,b)]
((k,v):xs) +<+ ys
    | elem k (map fst ys) = xs +<+ ys
    | otherwise = (k,v) : xs +<+ ys
[] +<+ ys = ys
--
getLiCtx :: Env -> Ctx
getLiCtx (Env x _) = x
getNlCtx :: Env -> Ctx
getNlCtx (Env _ y) = y
--
headL :: Env -> Maybe (Var, Val)
headL (Env (x : xs) _) = Just x
headL (Env [] _) = Nothing
headN :: Env -> Maybe (Var, Val)
headN (Env _ (y : ys)) = Just y
headN (Env _ []) = Nothing
--
consL :: (Var, Val) -> Env -> Env
consL vv (Env lis nls) = (Env (vv : lis) nls)
consN :: (Var, Val) -> Env  -> Env
consN vv (Env lis nls) = (Env lis (vv : nls))
--
