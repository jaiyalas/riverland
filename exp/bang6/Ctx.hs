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
data CtxError a = CtxExhausted {srcSwichEnv :: CtxSwitch, inKey :: a}
instance (Show a) => Show (CtxError a) where
    show ceh = "[Environment "++(show $ srcSwichEnv ceh)++" exhausted]: key "++
                (show $ inKey ceh)++
                " cannot be found"
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
lookupCtx :: (Eq a, Show a) => CtxSwitch -> Ctx a b -> a -> Except (CtxError a) b
lookupCtx Linear (Ctx ((v2, val) : lis) nls) v1
    | v1 == v2 = return val
    | otherwise = lookupCtx Linear (Ctx lis nls) v1
lookupCtx Normal (Ctx lis ((v2, val) : nls)) v1
    | v1 == v2 = return val
    | otherwise = lookupCtx Normal (Ctx lis nls) v1
lookupCtx Linear (Ctx [] _) v1 = throwError $ CtxExhausted Linear v1
lookupCtx Normal (Ctx _ []) v1 = throwError $ CtxExhausted Normal v1
--
insertCtx :: Eq a => ((c,b) -> a) -> CtxSwitch -> (c,b) -> Ctx a b -> Ctx a b
insertCtx f Linear x@(c,b) (Ctx ls ns) = Ctx
    ((f x, b) : filter ((/= (f x)) . fst) ls) ns
insertCtx f Normal x@(c,b) (Ctx ls ns) = Ctx
    ls ((f x, b) : filter ((/= (f x)) . fst) ns)
--
