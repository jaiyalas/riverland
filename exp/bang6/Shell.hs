module Shell where
--
import Types
import Expr
import Error
import Func
import Eval
import Typing
--
import Control.Monad.Except
import Control.Monad.Reader
--
run :: Expr -> Either ErrorMsg Val
run e = (flip runReader) mempty
      $ runExceptT (eval e)

ty :: Expr -> Either ErrorMsg Typ
ty e = (flip runReader) mempty
      $ runExceptT (typeof e)

test1 = prelude
     $ LetIn (Var "x") (Lit $ N $ int2nat 0)
     $ appRTo ("succ", "x") "y"
     $ (Var "y")

test2 = prelude
      $ (BVar "succ")
