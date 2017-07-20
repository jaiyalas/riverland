module Expr where
--
import Data.List (find)
import Data.Bifunctor
import Control.Monad.Reader (Reader(..))
--
import Debug.Trace
--
type Name = String
--
data Val
    = N Int
    | B Bool
    | Pr Val Val
    | Clos Name Typ Term Typ (DualEnv Val)
    deriving (Show, Eq)
--
data Typ
    = TNat
    | TBool
    | TProd Typ Typ
    | TFun Typ Typ
    deriving (Show, Eq)
--
data Case = (:~>) MTerm Term deriving (Show, Eq)
--
type MTerm = Term
type VTerm = Term
--
data Term
    = Lit Val
    | Var  Name
    | BVar Name
    --
    | Succ Term
    | Pair Term Term
    | Abs Name Typ Term Typ
    | App (Term, Term)
    --
    | LetIn MTerm Term Term
    | RecIn MTerm Term Term
    | BanIn MTerm Term Term
    | DupIn MTerm Term Term
    | AppIn MTerm (Term, Term) Term --
    --
    | Match VTerm [Case]
    | MatEq VTerm Case Case
    --
    deriving (Show, Eq)
    --
--
type Compt a = Reader (DualEnv a) a
--
type Cont = Compt Val -> Compt Val
--
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
--
type DualEnv v =
    ( Env Name v  -- ^ normal
    , Env Name v) -- ^ linear
consL :: (Name, v) -> (DualEnv v) -> (DualEnv v)
consL nv = bimap id ([nv] +>+)
consN :: (Name, v) -> (DualEnv v) -> (DualEnv v)
consN nv = bimap ([nv] +>+) id
--
type Env k v = [(k, v)]
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

--
peekByKey :: Eq k => k -> Env k v -> Maybe v
rmByKey   :: Eq k => k -> Env k v -> Env k v
popByKey  :: Eq k => k -> Env k v -> (Maybe v, Env k v)
--
peekByKey k = fmap snd . find ((k==).fst)
rmByKey   k = filter ((k==).fst)
popByKey  k = bimap (peekByKey k) (rmByKey k) . dup
--
dup :: a -> (a, a)
dup x = (x, x)
--
