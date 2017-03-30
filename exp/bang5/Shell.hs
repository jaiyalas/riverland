module Shell where
--
import Types
import Expr
import Ctx
import CtxOp
import Func
import Match
import Eval
import Rval
--
intv :: Int -> Val
intv = N . int2nat
prv :: (Int,Int) -> Val
prv (i,j) = Pr (intv i) (intv j)
-- --
run_ :: FunName -> Val -> (Val, Ctx Var (Val,Typ))
run_ fname args = eval mempty $ prelude $
    AppIn (mat "res")
        (fname, Lit args)
        (Term $ var "res")
--
run :: FunName -> Val -> Val
run fn = fst . (run_ fn)
-- --
rrun_ :: FunName -> Val -> Ctx Var (Val,Typ)
rrun_ fname arg = rval mempty arg $
    prelude $
    AppIn (mat "res") (fname, var "input") $
    Term $ var "res"
--
rrun :: FunName -> Val -> Val
rrun fname arg = subsVal Linear (rrun_ fname arg) (var "input")
