module Shell where
--
import Expr
import Env
import Func
import Match
import Eval
-- import Rval
--
intv :: Int -> Val
intv = N . int2nat
prv :: (Int,Int) -> Val
prv (i,j) = Pr (intv i) (intv j)
-- --
run_ :: FunName -> Val -> (Val, Env)
run_ fname args = eval mempty $ prelude $
    AppIn (mat "res")
        (fname, Lit args)
        (Term $ var "res")
--
run :: FunName -> Val -> Val
run fn = fst . (run_ fn)
-- --
