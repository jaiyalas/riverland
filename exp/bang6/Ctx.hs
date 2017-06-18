module Ctx where
--
import Control.Monad.Except
--
import Data.List (lookup)

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
    lookupN ctx k >>=
        -- pop from normal context == lookup
        (\v -> return (v, Ctx ls ns))
        -- (\v -> return (v, Ctx ls (filter ((/= k) . fst) ns)))
popCtx Linear ctx@(Ctx ls ns) k =
    lookupL ctx k >>=
        (\v -> return (v, Ctx (filter ((/= k) . fst) ls) ns))
--
splitEnv :: Eq k
         => [k] -- ^ targeting names
         -> Env k v
         -> Except (CtxInternalError k) ( Env k v
                                        , Env k v)
splitEnv ks xs = splitEnv' ks xs mempty
--
splitEnv' :: Eq k => [k]   -- ^ targeting key
                -> Env k v -- ^ input env
                -> Env k v -- ^ (accumulating) filtered env
                -> Except (CtxInternalError k) ( Env k v
                                               , Env k v)
splitEnv' [] xs ys = return (xs, ys)
splitEnv' (k:ks) xs ys = maybe
    (throwError (CtxError k))
    (\v -> splitEnv' ks (filter ((/= k).fst) xs) ((k,v):ys))
    (lookup k xs)
--
splitCtx :: Eq k
         => [k] -- ^ linear
         -> Ctx k v
         -> Except (CtxInternalError k) ( Ctx k v   -- ^ selected
                                        , Ctx k v ) -- ^ remains
splitCtx lns (Ctx ls ns) = do
    (leftLEnv, selectedLEnv) <- splitEnv lns ls
    return $ (Ctx selectedLEnv ns, Ctx leftLEnv ns)
--
-- splitCtx :: Eq k
--          => [k] -- ^ linear
--          -> [k] -- ^ normal
--          -> Ctx k v
--          -> Except (CtxInternalError k) ( Ctx k v   -- ^ selected
--                                         , Ctx k v ) -- ^ remains
-- splitCtx lns nns (Ctx ls ns) = do
--     (leftLEnv, selectedLEnv) <- splitEnv lns ls
--     (leftNEnv, selectedNEnv) <- splitEnv nns ns
--     return $ (Ctx selectedLEnv selectedNEnv, Ctx leftLEnv leftNEnv)
--
data CtxInternalError k
    = CtxError k
    deriving (Show, Eq)







--
