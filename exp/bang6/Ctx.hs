module Ctx where
--
import Control.Monad.Except
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
--
instance Eq a => Monoid (Ctx a b) where
    mempty = Ctx [] []
    mappend (Ctx xs ys) (Ctx xs2 ys2) =
        Ctx (xs +>+ xs2) (ys +>+ ys2)
--
consL :: (a,b) -> Ctx a b -> Ctx a b
consL vv (Ctx lis nls) = (Ctx (vv : lis) nls)
consN :: (a,b) -> Ctx a b -> Ctx a b
consN vv (Ctx lis nls) = (Ctx lis (vv : nls))
--

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
lookupCtx :: (Eq k, Show k) => CtxSwitch -> Ctx k v -> k -> Maybe v
lookupCtx Linear (Ctx ((v2, val) : lis) nls) v1
    | v1 == v2 = return val
    | otherwise = lookupCtx Linear (Ctx lis nls) v1
lookupCtx Normal (Ctx lis ((v2, val) : nls)) v1
    | v1 == v2 = return val
    | otherwise = lookupCtx Normal (Ctx lis nls) v1
lookupCtx Linear (Ctx [] _) v1 = Nothing
lookupCtx Normal (Ctx _ []) v1 = Nothing
--
lookupL :: (Eq k, Show k) => Ctx k v -> k -> Maybe v
lookupL = lookupCtx Linear
lookupN :: (Eq k, Show k) => Ctx k v -> k -> Maybe v
lookupN = lookupCtx Normal
--


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
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
--


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
popCtx :: (Eq k, Show k)
       => CtxSwitch
       -> Ctx k v
       -> k
       -> Maybe (v, Ctx k v)
popCtx Normal ctx@(Ctx ls ns) k =
    lookupL ctx k >>=
        (\v -> return (v, Ctx ls (filter ((/= k) . fst) ns)))
popCtx Linear ctx@(Ctx ls ns) k =
    lookupL ctx k >>=
        (\v -> return (v, Ctx (filter ((/= k) . fst) ls) ns))
--

-- {-# LANGUAGE MultiParamTypeClasses #-}
-- https://www.schoolofhaskell.com/school/to-infinity-and-beyond/pick-of-the-week/profunctors
-- https://wiki.haskell.org/GHC/Type_families


-- class Splitable f where
--     split :: [a]
--
-- splitCtx :: [VName] --
--          -> [VName]
--          -> Ctx
--          -> Except SomeError (Ctx, Ctx)
-- --
-- splitCtx ns1 ns2 ctx










--
