module Rval where
--
import Data.List (find)
import Data.Maybe (fromJust)
import Data.Bifunctor
import Control.Monad.Reader
--
import Expr
--
-- rval0 :: Val -> Term -> Reader (DualEnv Typ) (DualEnv Typ)
-- --
-- rval0 v (Var name)  = asks (consL (name, v))
-- rval0 v (BVar name) = asks (consN (name, v))
-- -- --
-- rval0 (N 0) (Succ _) = error "yo"
-- rval0 (N n) (Succ t) = rval0 (N (n-1)) t
-- rval0 (Pr v1 v2) (Pair t1 t2) = rval0 v1 t1 >>= rval0 v2 t2
-- --
-- rval0 (Clos name1 inTyp1 func1 outTyp1 localEnv)
--       (Abs  name2 inTyp2 func2 outTyp2) = do
--           return mempty
-- rval0 v (App (fun, arg)) = undefined
-- -- --
-- rval0 v (LetIn (Var name) t next) = do
--     envNext <- rval0 v next
--     let v' = peekByKey name (snd envNext)
--     local (const envNext) (rval0 v' t)
-- -- rval0 v (LetIn (Pair t1 t2) t next) = do
-- rval0 v (LetIn (Pair (Var x) (Var y)) t next) = do
--     envNext <- rval0 v next
--     let v1 = peekByKey x (snd envNext)
--         v2 = peekByKey y (snd envNext)
--     local (const envNext) (rval0 (Pr v1 v2) t)
-- rval0 v (DupIn (Pair (Var x) (Var y)) t next) = do
--     envNext <- rval0 v next
--     let v1 = peekByKey x (snd envNext)
--         v2 = peekByKey y (snd envNext)
--     if v1 == v2
--         then local (const envNext) (rval0 v1 t)
--         else error "reversing dupin failed"
-- rval0 v (BanIn (BVar x) t next) = do
--     envNext <- rval0 v next
--     let v1 = peekByKey x (fst envNext)
--     local (const envNext) (rval0 v1 t)
-- --
-- rval0 v (RecIn (BVar name) t next) = do
--     envNext <- rval0 v next
--     let funClos = fromJust $ peekByKey name (fst nextEnv)
--     local (const envNext) (rval funClos t)
-- -- --
-- rval0 v (Match var cases) = undefined
-- rval0 v (MatEq var caseEq caseNEq) = undefined
-- rval0 _ _ = error "yooooo"
--
--
--
-- --
-- oracle :: Val -> Term -> Bool
-- oracle (Pr vl vr) (DupIn mt vt expr)
--     | vl == vr = revMatch (Pr vl vr) (dss expr)
--     | otherwise = False
-- oracle v expr = revMatch v (dss expr)
-- -- --
--
-- -- reversed pattern matching
-- revMatch :: Val -> Term -> Bool
-- revMatch (B b1) (Lit (B b2)) = b1 == b2
-- -- 0 <m> 0
-- revMatch (N 0) (Lit 0) = True
-- -- S n <m> S n
-- revMatch (N n) (Succ vt) = revMatch (N (n-1)) vt
-- -- pair
-- revMatch (Pr v1 v2) (Pair vt1 vt2) =
--     (revMatch v1 vt1) && (revMatch v2 vt2)
-- -- irrefusable
-- revMatch _ (Var _) = True
-- -- revMatch _ (BVar _) = True -- ?
-- revMatch _ _ = False
-- -- --
--
-- -- headConstructor, aka de-structural-syntax
-- dss :: Term -> Term
-- dss (Var vt) = Var vt
-- dss (BVar vt) = BVar vt
-- dss (BVar vt) = BVar vt
-- --
-- dss (Pair e1 e2) = Prod (dss e1) (dss e2)
-- dss (LetIn _ _ expr) = dss expr
-- dss (App _ _ expr) = dss expr
-- dss (DupIn _ _ expr) = dss expr
-- dss (Abs _ _ _) = error $
--     "<<dss | Illegal syntax>>\n"++
--     "\t\"Lambda\" cannot be DSS-fied"
-- dss (Match _ _) = error $
--     "<<dss | Illegal syntax>>\n"++
--     "\t\"Match\" cannot be DSS-fied"
-- dss (MatEq _ _ _) = error $
--     "<<dss | Illegal syntax>>\n"++
--     "\t\"MatEq\" cannot be DSS-fied"
-- --
--
-- -- find val by vt; then create val by mt
-- vmGen :: Ctx Var (Val,Typ) -> VTerm -> MTerm -> Ctx Var (Val,Typ)
-- vmGen = \ env vt mt -> vmGenWith env vt mt id
-- --
-- vmGenWith :: Ctx Var (Val,Typ) -> VTerm -> MTerm -> (Val -> Val) -> Ctx Var (Val,Typ)
-- vmGenWith nev vt mt f =
--     insertVal Linear nev mt $ f $ subsVal Linear nev vt
