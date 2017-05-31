module Shell where
--
import Expr
import Error
import Func
import Eval
--
import Control.Monad.Except
import Control.Monad.Reader
--
run :: Expr -> Either ErrorMsg Val
run e = (flip runReader) mempty
      $ runExceptT (eval e)

test = prelude
     $ LetIn (Var "x") (Lit $ N $ int2nat 0)
     $ appRTo ("succ", "x") "y"
     $ (Var "y")
