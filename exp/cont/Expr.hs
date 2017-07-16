module Ctx where
--
import Data.List (find)
import Data.Maybe (fromJust)
import Data.Bifunctor
import Control.Monad.Reader
--
type Name = String
--
data Val = Val Int | Clos Name Term Environment deriving (Show, Eq)
--
data Term
    = Lit Int
    | Var Name
    | BVar Name
    | Abs Name Term
    | App Term Term
    deriving (Show, Eq)
    --
    -- RecIn :: Term -> Term -> Term
    -- LetIn :: Term -> Term -> Term
    -- BanIn :: Term -> Term
    --
--
type ComptVal = Reader Environment Val
--
type Cont = ComptVal -> ComptVal
--
eval :: Term -> Cont -> ComptVal
eval (Lit n) k = k $ return $ Val n
eval (Var name) k =
    k $ asks (fromJust . peekByKey name . snd)
eval (BVar name) k =
    k $ asks (fromJust . peekByKey name . fst)
eval (Abs name func) k =
    k $ asks (Clos name func)
eval (App func arg) k =
    eval func
        (>>= (\(Clos name fbody localEnv) ->
            eval arg
                (>>= (\v -> local (const $ (name, v) `consL` localEnv) (eval fbody k))
                )
        ))
--
--
type Environment =
    ( Env Name Val  -- ^ normal
    , Env Name Val) -- ^ linear
consL :: (Name, Val) ->  Environment -> Environment
consL nv (ns, ls) = (ns, nv:ls)
consN :: (Name, Val) ->  Environment -> Environment
consN nv (ns, ls) = (nv:ns, ls)
--
type Env k v = [(k, v)]
--
peekByKey :: Eq k => k -> Env k v -> Maybe v
rmByKey   :: Eq k => k -> Env k v -> Env k v
popByKey  :: Eq k => k -> Env k v -> (Maybe v, Env k v)
--
peekByKey k = fmap snd . find ((k==).fst)
rmByKey   k = filter ((k==).fst)
popByKey  k = bimap (peekByKey k) (rmByKey k) . dup
--


--
dup :: a -> (a, a)
dup x = (x, x)
