module Shell where
--
import Types
import Expr
import Error
import Func
import Eval
import Typing
--
import Data.List
--
import Control.Monad.Except
import Control.Monad.Reader
--
exec :: Expr -> IO () -- Either ErrorMsg (Val, Typ)
exec e = do
    putStrLn $ show $ run e
    putStrLn $ show $ ty e
--
run :: Expr -> Either ErrorMsg Val
run e = (flip runReader) mempty
      $ runExceptT (eval e)
--
ty :: Expr -> Either ErrorMsg Typ
ty e = (flip runReader) mempty
      $ runExceptT (typeof e)
--
test1 = prelude
     $ LetIn (Var "x") (Lit $ N $ int2nat 0)
     $ appRTo ("succ", "x") "y"
     $ (Var "y")
--
test2 = prelude
      $ (BVar "succ")
--
test3 = prelude
      $ LetIn (Var "x") (Lit $ N $ int2nat 3)
      $ LetIn (Var "y") (Lit $ N $ int2nat 4)
      $ LetIn (Var "p") (pairVar "x" "y")
      $ appRTo ("plus", "p") "return"
      $ Var "return"
--
test41 = LetIn (Var "x") (Lit $ N $ int2nat 1)
       $ LetIn (Var "p") (pairVar "x" "x")
       $ Var "p"
--
test42 = LetIn (Var "x") (Lit $ N $ int2nat 1)
       $ BanIn (BVar "y") (Var "x")
       $ LetIn (Var "p") (Pair (BVar "y") (BVar "y"))
       $ Var "p"
--
test43 = LetIn (Var "x") (Lit $ N $ int2nat 1)
       $ BanIn (BVar "x") (Var "x")
       $ LetIn (Var "p") (Pair (BVar "x") (BVar "x"))
       $ Var "p"
--
test5 = LetIn (Var "x") (Lit $ N $ int2nat 3)
      $ LetIn (Var "y") (Lit $ N $ int2nat 2)
      $ LetIn (Var "p") (pairVar "x" "y")
      $ Var "p"
--
test6 = LetIn (Var "x") (Lit $ N $ int2nat 1)
      $ Var "x"




--
useless01 :: Expr -> Expr
useless01 e = foldr ($) e
         $ fmap (\x -> LetIn
                         (Var ([x]))
                         (Lit $ N $ int2nat $ fromEnum x))
         $ ['a'..'z']
--
