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
      $ LetIn (Var "x") (Lit $ N $ int2nat 1)
      $ LetIn (Var "y") (Lit $ N $ int2nat 9)
      $ LetIn (Var "p") (pairVar "x" "y")
      $ appRTo ("plus", "p") "return"
      $ Var "return"
--
test4 = prelude
      $ LetIn (Var "x") (Lit $ N $ int2nat 9)
      $ LetIn (Var "y") (Lit $ N $ int2nat 3)
      $ LetIn (Var "p") (pairVar "x" "y")
      $ appRTo ("plus", "p") "return"
      $ Var "return"
--
test5 = LetIn (Var "x") (Lit $ N $ int2nat 1)
      $ LetIn (Var "y") (Lit $ N $ int2nat 9)
      $ LetIn (Var "p") (pairVar "x" "y")
      $ Var "p"
--
test6 = LetIn (Var "x") (Lit $ N $ int2nat 1)
      $ Var "x"
-- names :: [String] -> [String]
-- names xs = xs ++ zipWith (++) (smalloop xs) (foo xs (names xs))
--
-- foo :: [a] -> [b] -> [b]
-- foo xs ys = concat $ map (toEnough (length xs)) ys
--
-- toEnough :: Int -> a -> [a]
-- toEnough n = take n . repeat
--
-- smalloop xs = xs ++ smalloop xs
--
-- -- [ map (c ++) nns | c <- nns0]




--
useless01 :: Expr -> Expr
useless01 e = foldr ($) e
         $ fmap (\x -> LetIn
                         (Var ([x]))
                         (Lit $ N $ int2nat $ fromEnum x))
         $ ['a'..'z']
--
