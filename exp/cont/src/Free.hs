module Free where
--
import Expr
import Control.Monad
import Data.Bifunctor
import Data.Maybe (maybe)
--
splitEnvWithTerms :: Eq v => (Term, Term) -> Env Name v -> (Env Name v, Env Name v)
splitEnvWithTerms (t1, t2) ls =
    let fvT1 = snd $ freeVar t1
        fvT2 = snd $ freeVar t2
        (lsLeft, lsT1) = splitEnv fvT1 ls
        (lsLeft', lsT2) = splitEnv fvT2 lsLeft
    in if lsLeft' == []
        then (lsT1, lsT2)
        else error "dirty splitEnvWithTerms"

--
subDEnv :: Term -> DualEnv v ->  DualEnv v
subDEnv t (ns,ls) =
    -- normal nev remains intact
    ( ns
    -- sub linear nev
    , snd $ splitEnv (snd $ freeVar t) ls)
--
splitEnv :: Eq k
         => [k] -- ^ targeting key
         -> Env k v -- ^ input env
         -> (Env k v, Env k v)
splitEnv ks xs = splitEnv' ks xs mempty
--
splitEnv' :: Eq k
          => [k]   -- ^ targeting key
          -> Env k v -- ^ input env
          -> Env k v -- ^ (accumulating) filtered env
          -> (Env k v, Env k v)
splitEnv' [] xs ys = (xs, ys)
splitEnv' (k:ks) xs ys = maybe
    (error "[failure] split env")
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
--
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
freeVar (AppIn vn (funE, argE) next) =
    let (ns1, ls1) = freeVar next
        (ns2, ls2) = freeVar argE
        (ns3, ls3) = freeVar funE
        (xs, ys) = (freeVar vn)
        foo1 = filter ((flip notElem) xs)
        foo2 = filter ((flip notElem) ys)
    in bimap foo1 foo2
        ( ns1 `mappend` ns2 `mappend` ns3
        , ls1 `mappend` ls2 `mappend` ls3)
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
