module Free where
--
import Expr
import Control.Monad
import Data.Bifunctor
import Data.Maybe (maybe, catMaybes)
--
import Debug.Trace
--
splitEnvWithTerm :: (Eq v, Show v)
                  => Term -> Env Name v -> (Env Name v, Env Name v)
splitEnvWithTerm t ls =
    let (lsLeft, lst) = splitEnv (snd $ freeVar t) ls
    in (lst, lsLeft)

splitEnvWith2Terms :: (Eq v, Show v)
                  => (Term, Term) -> Env Name v -> (Env Name v, Env Name v)
splitEnvWith2Terms (t1, t2) ls =
    let fvT1 = snd $ freeVar t1
        fvT2 = snd $ freeVar t2
        (lsLeft, lsT1)  = splitEnv fvT1 ls
        (lsLeft', lsT2) = splitEnv fvT2 lsLeft
    in if lsLeft' == []
        then (lsT1, lsT2)
        else error "dirty(splitEnvWithTerms)"
--
subDEnv :: (Eq v, Show v) => Term -> DualEnv v ->  DualEnv v
subDEnv t (ns,ls) =
    -- normal nev remains intact
    ( ns
    -- sub linear nev
    , snd $ splitEnv (snd $ freeVar t) ls)
--
splitEnv :: (Eq k, Show k, Show v)
         => [k] -- ^ targeting key
         -> Env k v -- ^ input env
         -> (Env k v, Env k v)
splitEnv ks xs = splitEnv' ks xs mempty
--
splitEnv' :: (Eq k, Show k, Show v)
          => [k]   -- ^ targeting key
          -> Env k v -- ^ input env
          -> Env k v -- ^ (accumulating) filtered env
          -> (Env k v, Env k v)
splitEnv' [] xs ys = (xs, ys)
splitEnv' (k:ks) xs ys = maybe
    (error $ "[splitEnv'] " ++ (show k) ++ " cannot be found within " ++ (show xs))
    (\v -> bimap id ((k, v):) (splitEnv' ks (filter ((/=k).fst) xs) ys))
    (lookup k xs)
--
freeVar :: Term -> ( [Name]  -- ^ normal
                   , [Name]) -- ^ linear
freeVar (Var  vn) = (mzero ,[vn])
freeVar (BVar vn) = ([vn], mzero)
freeVar (Lit _) = (mzero, mzero)
freeVar (Succ e) = freeVar e
--
freeVar (Pair e1 e2) =
    let (ns1, ls1) = freeVar e1
        (ns2, ls2) = freeVar e2
    in (ns1 `mappend` ns2, ls1 `mappend` ls2)
--
freeVar (App (funE, argE)) =
    let (ns1, ls1) = freeVar argE
        (ns2, ls2) = freeVar funE
    in (ns1 `mappend` ns2, ls1 `mappend` ls2)
--
freeVar (Abs vn tyIn fbody tyOut) =
    bimap (filter (/= vn)) (filter (/= vn)) $ freeVar fbody
-- let x = (1 + a) in (x + 1)
freeVar (LetIn vn e next) =
    let (ns1, ls1) = freeVar next
        (ns2, ls2) = freeVar e
        (xs, ys) = freeVar vn
        foo1 = filter ((flip notElem) xs)
        foo2 = filter ((flip notElem) ys)
    in bimap foo1 foo2 (ns1 `mappend` ns2, ls1 `mappend` ls2)
freeVar (RecIn vn e next) = freeVar (LetIn vn e next)
freeVar (BanIn vn e next) = freeVar (LetIn vn e next)
freeVar (DupIn vn e next) = freeVar (LetIn vn e next)
--
-- freeVar (AppIn vn (funE, argE) next) =
--     let (ns1, ls1) = freeVar next
--         (ns2, ls2) = freeVar argE
--         (ns3, ls3) = freeVar funE
--         (xs, ys) = (freeVar vn)
--         foo1 = filter ((flip notElem) xs)
--         foo2 = filter ((flip notElem) ys)
--     in bimap foo1 foo2
--         ( ns1 `mappend` ns2 `mappend` ns3
--         , ls1 `mappend` ls2 `mappend` ls3)
freeVar (Match vn cases) =
    let (ns2, ls2) = freeVar vn
        (ns, ls)   = bimap concat concat $ unzip (map fvCase cases)
    in ( filter ((flip notElem) ns2) ns
       , filter ((flip notElem) ls2) ls )
freeVar (MatEq vn case1 case2) =
    freeVar (Match vn [case1,case2])
--
fvCase :: Case -> ( [Name]  -- ^ normal
                  , [Name]) -- ^ linear
fvCase (e :~> next) =
    let (xs, ys)   = freeVar e
        (ns1, ls1) = freeVar next
    in ( filter ((flip notElem) xs) ns1
       , filter ((flip notElem) ys) ls1 )
--
-- splitDualEnvPlus :: [Name]
--                  -> DualEnv v
--                  -> (DualEnv v, DualEnv v)
-- splitDualEnvPlus ks (ns, ls) =
--     let (ls1, ls2) = splitEnv ks ls
--     in ((ns, ls1), (ns, ls2))
-- --
-- splitDualEnv :: [Name]
--              -> DualEnv v
--              -> (DualEnv v, DualEnv v)
-- splitDualEnv ks (ns, ls) =
--     let (ns1, ns2) = splitEnv ks ns
--         (ls1, ls2) = splitEnv ks ls
--     in ( (ns1, ls1)
--        , (ns2, ls2) )

--
--
-- casesMatch :: Eq a => a -> [Case] -> Maybe [DualEnv a]
-- casesMatch v
--     = (\x -> if null x then Nothing else Just x)
--     . catMaybes . fmap (matching v . casePattern)
-- --
-- dss :: Term -> [Pattern]
-- dss (Lit v) = return (Lit v)
-- dss (Var vt) = return (Var vt)
-- dss (BVar vt) = return (BVar vt)
-- --
-- dss (Succ t) = fmap Succ (dss t)
-- dss (Pair e1 e2) = zipWith Pair (dss e1) (dss e2)
-- --
-- dss (Abs _ _ _ _) = error "un-dssable"
-- dss (App _)  = error "un-dssable"
-- --
-- dss (LetIn _ _ next) = dss next
-- dss (RecIn _ _ next) = dss next
-- dss (DupIn _ _ next) = dss next
-- dss (BanIn _ _ next) = dss next
-- -- -- hmmmmmmm..
-- dss (Match _ cs) =
--     concat $ fmap (dss . caseBody) cs
-- dss (MatEq t ceq cneq) =
--     dss (Match t [ceq, cneq])
-- --
-- data CaseExt = CaseExt Pattern [Term -> Term] Pattern
-- caseExt :: Case -> CaseExt
-- caseExt (p :~> t) = CaseExt p path p'
--     where (path, p') = epath t
-- -- errrr... zipper?
-- epath :: Term -> ([Term -> Term], Pattern)
-- epath t@(Lit _)  = ([], t)
-- epath t@(Var _)  = ([], t)
-- epath t@(BVar _) = ([], t)
-- --
-- epath t@(Succ _) = fmap Succ (dss t)
-- epath t@(Pair _ _) = zipWith Pair (dss e1) (dss e2)
-- --
-- epath (Abs _ _ _ _) = error "un-dssable"
-- epath (App _)  = error "un-dssable"
-- --
-- epath (LetIn var t next) =
--     let (xs, node) = epath next in ((LetIn var t) : xs, node)
-- epath (RecIn var t next) =
--     let (xs, node) = epath next in ((RecIn var t) : xs, node)
-- epath (DupIn var t next) =
--     let (xs, node) = epath next in ((DupIn var t) : xs, node)
-- epath (BanIn var t next) =
--     let (xs, node) = epath next in ((BanIn var t) : xs, node)
-- --
-- epath (Match var cs) =
--
--
-- --
-- matchCase :: Eq a => a -> Case -> Maybe (DualEnv a, Term)
-- matchCase v (p :~> e) =
--     match v p >>= \x -> return $ Just (x, e)
-- --
-- match :: Eq a => a -> Pattern -> Maybe (DualEnv a)
-- match val (Lit v)
--     | val == v  = return mempty
--     | otherwise = Nothing
-- match val (Var vt)  =
--     return $ (val, Var vt) `consL` mempty
-- match val (BVar vt) =
--     return $ (val, Var vt) `consN` mempty
-- --
-- match (N 0) (Succ vt) = error "not a pattern"
-- match (N n) (Succ vt) = match (N (n - 1)) vt
-- --
-- match (Pr v1 v2) (Pair va vb) =
--     match v1 va ++ match v2 vb
-- --
-- match _ _ = error "not a pattern"
--
-- --
--
--
-- data Rose a = RoseNode a [Rose a]
-- roseLift


--
