module Shell where
--
import Expr
import Ctx
import Func
import Pat
import Eval
import Rval
--
-- TODO: add lambda and function (non-linear) context
--
tNeg :: (Val, Env)
tNeg = eval [(Var "#0", B False)] negExpr

tSucc :: Int -> (Val, Env)
tSucc m = eval [(Var "#0", N $ int2nat m)] succExpr

tPlus :: (Int, Int) -> (Val, Env)
tPlus (m,n) = eval [(Var "#0", Pair (N $ int2nat m) (N $ int2nat n))] plusExpr

tPlusR :: (Int, Int) -> (Val, Env)
tPlusR (m,n) = eval [(Var "#0", Pair (N $ int2nat m) (N $ int2nat n))] plusRExpr

--

rSucc :: Int -> Env
rSucc n = rval ( N $ int2nat n, []) succExpr

rPlus :: (Int, Int) -> Env
rPlus (m, n) = rval ( Pair (N $ int2nat m) (N $ int2nat n)
                     , []) plusExpr
