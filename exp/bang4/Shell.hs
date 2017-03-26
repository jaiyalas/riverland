module Shell where
--
import Expr
import Env
import Func
import Pat
import Eval
import Rval

run :: FunName -> Val -> Val
run fname args = fst $ run_ fname args

run_ :: FunName -> Val -> (Val, Env)
run_ fname args = eval mempty $ prelude $
    LetIn (mat "res") (Right (fname, Lit args)) (Term $ var "res")

rrun_ :: FunName -> Val -> Env
rrun_ fname arg = rval (arg, mempty) $
    prelude $
    LetIn (mat "res") (Right (fname, var "input")) $
    Term $ var "res"

rrun :: FunName -> Val -> Val
rrun fname arg = subs Linear (rrun_ fname arg) (var "input")

intv :: Int -> Val
intv = N . int2nat

prv :: (Int,Int) -> Val
prv (i,j) = Pr (intv i) (intv j)
