module Ctx
    ( -- * type
      Env(..)
    , Ctx(..)
    , CtxSwitch(..)
    -- * adding elements
    , consL
    , consN
    , insertCtx
    , insertL
    , insertN
    -- * querying elements
    , lookupCtx
    , lookupL
    , lookupN
    -- * poping element out
    , popCtx
    -- * spliting ctx into two
    , splitCtx
    -- * internal error msg
    , CtxInternalError(..)
    ) where
--
import Control.Monad.Except
--
import Data.Either (either)
import Data.List (lookup)
import Data.Bifunctor
--
--
type Env a b = [(a,b)]
--
(+>+) :: Eq a => Env a b -> Env a b -> Env a b
((k,v):xs) +>+ ys
    | elem k (map fst ys) = (k,v) : xs +>+ (filter ((/= k).fst) ys)
    | otherwise = (k,v) : xs +>+ ys
[] +>+ ys = ys
--
(+<+) :: Eq a => Env a b -> Env a b -> Env a b
((k,v):xs) +<+ ys
    | elem k (map fst ys) = xs +<+ ys
    | otherwise = (k,v) : xs +<+ ys
[] +<+ ys = ys
--
data Ctx a b = Ctx { getLEnv :: (Env a b)
                   , getNEnv :: (Env a b) }
             deriving (Show, Eq)
--
data CtxSwitch = Normal | Linear deriving (Show, Eq)
--
instance Eq a => Monoid (Ctx a b) where
    mempty = Ctx [] []
    mappend (Ctx xs ys) (Ctx xs2 ys2) =
        Ctx (xs +>+ xs2) (ys +>+ ys2)
instance Bifunctor Ctx where
    bimap f g (Ctx xs ys) =
        Ctx (map (\(a,b) -> (f a, g b)) xs)
            (map (\(a,b) -> (f a, g b)) ys)
--
filterCtx :: ((k,v) -> Bool) -> Ctx k v -> Ctx k v
filterCtx p (Ctx ls rs) = Ctx (filter p ls) (filter p rs)

rmCtx :: k -> Ctx k v -> Ctx k v
rmCtx k = filter ((/= k) . fst)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
consL :: (a,b) -> Ctx a b -> Ctx a b
consL vv (Ctx lis nls) = (Ctx (vv : lis) nls)
consN :: (a,b) -> Ctx a b -> Ctx a b
consN vv (Ctx lis nls) = (Ctx lis (vv : nls))
--
insertCtx :: Eq a => ((c,b) -> a) -> CtxSwitch -> (c,b) -> Ctx a b -> Ctx a b
insertCtx f Linear x@(c,b) (Ctx ls ns) = Ctx
    ((f x, b) : filter ((/= (f x)) . fst) ls) ns
insertCtx f Normal x@(c,b) (Ctx ls ns) = Ctx
    ls ((f x, b) : filter ((/= (f x)) . fst) ns)
--
insertL :: Eq a => a -> b -> Ctx a b -> Ctx a b
insertL x y = insertCtx fst Linear (x, y)
insertN :: Eq a => a -> b -> Ctx a b -> Ctx a b
insertN x y = insertCtx fst Normal (x, y)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
lookupCtx :: (Eq k, Show k)
          => CtxSwitch -> Ctx k v -> k
          -> Except (CtxInternalError k v) v
lookupCtx Linear (Ctx ((k2, val) : lis) nls) k1
    | k1 == k2 = return val
    | otherwise = lookupCtx Linear (Ctx lis nls) k1
lookupCtx Normal (Ctx lis ((k2, val) : nls)) k1
    | k1 == k2 = return val
    | otherwise = lookupCtx Normal (Ctx lis nls) k1
lookupCtx Linear (Ctx [] _) k1 = CtxExhausted k1
lookupCtx Normal (Ctx _ []) k1 = CtxExhausted k1
--
lookupL :: (Eq k, Show k)
        => Ctx k v -> k
        -> Except (CtxInternalError k v) v
lookupL = lookupCtx Linear
lookupN :: (Eq k, Show k)
        => Ctx k v -> k
        -> Except (CtxInternalError k v) v
lookupN = lookupCtx Normal
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
popCtx :: (Eq k, Show k)
       => CtxSwitch -> Ctx k v -> k
       -> Except (CtxInternalError k v) (v, Ctx k v)
popCtx Normal ctx k =
    mapExcept
        (either (Left . PopoutCtx)
                (\x -> Right (x, ctx)))
        (lookupN ctx k)
popCtx Linear ctx k =
    mapExcept
        (either (Left . PopoutCtx)
                (\x-> Right (x, filterCtx ((/=k).fst) ctx)))
        (lookupN ctx k)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- | underlying environment spliting
splitEnv' :: Eq k
          => [k]   -- ^ targeting key
          -> Env k v -- ^ input env
          -> Env k v -- ^ (accumulating) filtered env
          -> Except (CtxInternalError k v) (Env k v, Env k v)
splitEnv' [] xs ys = return (xs, ys)
splitEnv' (k:ks) xs ys = maybe
    (inErrCtx k)
    ( \v -> (splitEnv' ks xs ys) >>=
            return . bimap  ((k, v):) )
    (lookup k xs)
splitEnv :: Eq k
         => [k] -> Env k v
         -> Except (CtxInternalError k v) (Env k v, Env k v)
splitEnv ks xs = splitEnv' ks xs mempty
--
splitCtx :: Eq k
         => [k] -- ^ linear
         -> Ctx k v
         -> Except (CtxInternalError k v)
                ( Ctx k v   -- ^ selected
                , Ctx k v ) -- ^ remains
splitCtx lns (Ctx ls ns) = do
    (envLs, envRs) <- splitEnv lns ls
    return (Ctx envLs ns, Ctx envRs ns)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
data CtxInternalError k v
    = InCtxErr k
    -- | InErrCtxSplit k
    -- | InErrEnvSplit k
    -- | InErrCtxLookup k
    -- | InErrCtxPopout k
    | CtxExhausted k
    | PopoutCtx (CtxInternalError k v)
    deriving (Show, Eq)

--
-- inErrCtx :: k -> Except (CtxInternalError k) a
-- inErrCtx k  = throwError $ InErrCtx  k
-- inErrCtxSplit :: k -> Except (CtxInternalError k) a
-- inErrCtxSplit k  = throwError $ InErrCtxSplit  k
-- inErrEnvSplit :: k -> Except (CtxInternalError k) a
-- inErrEnvSplit k  = throwError $ InErrEnvSplit  k
-- inErrCtxLookup :: k -> Except (CtxInternalError k) a
-- inErrCtxLookup k = throwError $ InErrCtxLookup k
-- inErrCtxPopout :: k -> Except (CtxInternalError k) a
-- inErrCtxPopout k = throwError $ InErrCtxPopout k
--
