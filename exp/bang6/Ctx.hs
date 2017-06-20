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
    , InternalErrorCtx(..)
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
instance Bifunctor (Ctx k) where
    bimap f g (Ctx xs ys) = Ctx (f xs) (y ys)
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
          -> Except (CtxInternalError k) v
lookupCtx Linear (Ctx ((v2, val) : lis) nls) v1
    | v1 == v2 = return val
    | otherwise = lookupCtx Linear (Ctx lis nls) v1
lookupCtx Normal (Ctx lis ((v2, val) : nls)) v1
    | v1 == v2 = return val
    | otherwise = lookupCtx Normal (Ctx lis nls) v1
lookupCtx Linear (Ctx [] _) v1 = inErrCtxLookup v1
lookupCtx Normal (Ctx _ []) v1 = inErrCtxLookup v1
--
lookupL :: (Eq k, Show k)
        => Ctx k v -> k
        -> Except (CtxInternalError k) v
lookupL = lookupCtx Linear
lookupN :: (Eq k, Show k)
        => Ctx k v -> k
        -> Except (CtxInternalError k) v
lookupN = lookupCtx Normal
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
popCtx :: (Eq k, Show k)
       => CtxSwitch -> Ctx k v -> k
       -> Except (CtxInternalError k) (v, Ctx k v)
popCtx Normal ctx k =
    mapExcept
        (either (const (InErrCtxPopout k))
                (\x->(x, ctx)))
        (lookupN ctx k)
popCtx Linear ctx k =
    mapExcept
        (either (const (InErrCtxPopout k))
                (\x->(x, bimap noK id ctx)))
        (lookupN ctx k)
    where noK = filter ((/= k) . fst)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- | underlying environment spliting
splitEnv' :: Eq k
          => [k]   -- ^ targeting key
          -> Env k v -- ^ input env
          -> Env k v -- ^ (accumulating) filtered env
          -> Except (CtxInternalError k) (Env k v, Env k v)
splitEnv' [] xs ys = return (xs, ys)
splitEnv' (k:ks) xs ys = maybe
    (inErrEnvSplit k)
    (\v -> bimap (filter ((/= k) . fst)) ((k, v):) (splitEnv' ks xs ys))
    (lookup k xs)
splitEnv :: Eq k
         => [k] -> Env k v
         -> Except (CtxInternalError k) ( Env k v, Env k v)
splitEnv ks xs = splitEnv' ks xs mempty
--
splitCtx :: Eq k
         => [k] -- ^ linear
         -> Ctx k v
         -> Except (CtxInternalError k)
                ( Ctx k v   -- ^ selected
                , Ctx k v ) -- ^ remains
splitCtx lns (Ctx ls ns) =
    mapExcept (either id (bimap ((flip Ctx) ns) ((flip Ctx) ns)))
              (splitEnv lns ls)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
data InternalErrorCtx k
    = InErrCtxSplit k
    | InErrEnvSplit k
    | InErrCtxLookup k
    | InErrCtxPopout k
    deriving (Show, Eq)
--
inErrCtxSplit :: k -> Except (CtxInternalError k) a
inErrCtxSplit k  = throwError $ InErrCtxSplit  k
inErrEnvSplit :: k -> Except (CtxInternalError k) a
inErrEnvSplit k  = throwError $ InErrEnvSplit  k
inErrCtxLookup :: k -> Except (CtxInternalError k) a
inErrCtxLookup k = throwError $ InErrCtxLookup k
inErrCtxPopout :: k -> Except (CtxInternalError k) a
inErrCtxPopout k = throwError $ InErrCtxPopout k
--
