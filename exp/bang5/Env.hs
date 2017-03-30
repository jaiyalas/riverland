-- {-# LANGUAGE ExistentialQuantification #-}
-- {-# LANGUAGE RankNTypes #-}
-- {-# LANGUAGE StandaloneDeriving #-}
-- {-# LANGUAGE FlexibleInstances #-}
-- --
module Env where
--
-- import Data.Bifunctor
-- import Data.Functor.Classes (Show2(..), Eq2(..))
--
-- instance {-# OVERLAPPABLE #-} (Show a, Show b, Show2 p) => Show (p a b) where
--     showsPrec i x = liftShowsPrec2 showsPrec showList showsPrec showList i x
-- --
-- data Env' a b = forall p.( Bifunctor p
--                          , Show2 p
--                          ) => Env' [p a b]
-- --
-- deriving instance {-# OVERLAPPABLE #-} (Show a, Show b) => Show (Env a b)
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
-- -- data Ctx a b = Ctx (Env a b) (Env a b) deriving (Show, Eq)
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
--
consL :: (a,b) -> Ctx a b -> Ctx a b
consL vv (Ctx lis nls) = (Ctx (vv : lis) nls)
consN :: (a,b) -> Ctx a b -> Ctx a b
consN vv (Ctx lis nls) = (Ctx lis (vv : nls))
--
lookupCtx :: Eq a => CtxSwitch -> Ctx a b -> a -> b
lookupCtx Linear (Env ((v2, val) : lis) nls) v1
    | v1 == v2 = val
    | otherwise = lookupCtx Linear (Env lis nls) v1
--
lookupCtx Linear (Env [] _) v1 = error $
    "<< raccess | Environment exhausted >>\n"++
    "\tCannot find (" ++ (show v1) ++ ") in linear context."
--
lookupCtx Normal (Env lis ((v2, val) : nls)) v1
    | v1 == v2 = val
    | otherwise = lookupCtx Normal (Env lis nls) v1
--
lookupCtx Normal (Env _ []) v1 = error $
    "<< raccess | Environment exhausted >>\n"++
    "\tCannot find (" ++ (show v1) ++ ") in normal context."
--    
