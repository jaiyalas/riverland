module RedB where
--
import Expr
import Func
import Subs
import Ctx
--
redBeta :: Env -> Expr -> (Val, Env)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
redBeta env (Term vt) =
    appSigma env vt
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
redBeta env (LetIn mt (Left vt) e) =
    let (val, env') = appSigma env vt
        newEnv = zipMatEnv mt val env'
    in redBeta newEnv e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
redBeta env (LetIn mt (Right (fun, vts)) e) =
    let fspec = findFun fun globalFuns
        (vals, env') = appSigmaList env vts []
        res = apply fspec vals
        newEnv = zipMatEnv mt res env'
    in redBeta newEnv e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- MTerm in dup will be limited in terms of Prod
-- VTerm in dup will be limited in terms of Atom
redBeta env (DupIn (Prod (Atom (Mat ma1)) (Atom (Mat ma2))) (Atom va) e) =
        let (val, env') = find va env
            newEnv = (Var ma2, val) : (Var ma1, val) : env'
        in redBeta newEnv e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
redBeta env (Match vt cases) =
    let (val, env1) = appSigma env vt
        (env2, e) = matching val cases
    in redBeta (env1 ++ env2) e
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
redBeta env (MatEq (Atom va1, Atom va2) case1 case2) =
    let (val1, env1) = find va1 env
        (val2, env2) = find va2 env1
    in if val1 == val2
        then case case1 of
            ((Atom (Mat ma)) :--> e1) -> redBeta ((Var ma, val2) : env2) e1
            ((NatS (Atom (Mat ma))) :--> e2) -> redBeta ((Var ma, redN val1) : env2) e2
        else case case2 of
            ((Prod mt1 mt2) :--> e1) ->
                let newEnv = zipMatEnv mt2 val2 $ zipMatEnv mt1 val1 $ env2
                in redBeta newEnv e1
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --
apply :: FSpec -> [Val] -> Val
apply (FSpec _ args body) vals =
    fst $ redBeta (foldr zipMatEnvC [] $ zip (fmap Atom args) vals) body
    -- we cannot check the equality of length of args and vals here.. :(
-- -- -- --
matching :: Val -> [Case] -> (Env, Expr)
--
matching (Pair v1 v2) (((Prod mt1 mt2) :--> e) : cs) =
    let env = zipMatEnv mt2 v2 $ zipMatEnv mt1 v1 []
    in (env, e)
--
matching (N nat)      (((Lit (N n)) :--> e) : cs)
    | nat == n = ([], e)
    | otherwise = matching (N nat) cs
--
matching (N nat)      (((Atom ma) :--> e) : cs) =
    (zipMatEnv (Atom ma) (N nat) [], e)
--
matching (N (S nat))  (((NatS mt) :--> e) : cs) =
    maybe (matching (N (S nat)) cs) id $ localMatchingN (N nat) (mt :--> e)
--
matching (B b)        (((Lit (B b')) :--> e) : cs)
    | b == b' = ([], e)
    | otherwise = matching (B b) cs
--
matching (B b)        (((Atom ma) :--> e) : cs) =
    (zipMatEnv (Atom ma) (B b) [], e)
--
matching val (_ : cs) = matching val cs
matching val [] = error $ "Non-exhaustive patterns for: " ++ (show val)
-- -- -- --
localMatchingN :: Val -> Case -> Maybe (Env, Expr)
localMatchingN (N n) ((Atom (Mat ma)) :--> e) = Just ([(Var ma, N n)], e)
localMatchingN (N n) ((Lit (N m)) :--> e)
    | n == m = Just ([], e)
    | otherwise = Nothing
localMatchingN (N (S nat)) ((NatS mt) :--> e) =
    localMatchingN (N nat) (mt :--> e)
localMatchingN _ _ = Nothing
--

test_neg = redBeta [(Var "#0", B False)] negExpr
test_plus m n = redBeta [(Var "#0", N $ int2nat m), (Var "#1", N $ int2nat n)] plusExpr
test_succ m = redBeta [(Var "#0", N $ int2nat m)] succExpr
test_plusR (m,n) = redBeta [(Var "#0", Pair (N $ int2nat m) (N $ int2nat n))] plusRExpr
