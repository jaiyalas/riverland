module Main where
--
import Control.Monad.Reader
import Test.Hspec
import Cont
--
main :: IO ()
main = testEnvUniqueness
--
testEnvUniqueness :: IO ()
testEnvUniqueness = hspec $ do
    describe "testEnvUniqueness" $ do
        it "let x = 10 in x" $
            run (LetIn (Var "x") (Lit (N 10)) (Var "x")) `shouldBe` (N 10)
        it "test1" $
            run test1 `shouldBe` (Pr (N 2) (N 5))

--
run :: Term -> Val
run e = runReader (eval1 e id) ([], [])
--
-- test = succExpr $ plusExpr
--      $ LetIn (Var "x") (Lit $ N 3)
--      $ appRTo ("succ", "x") "y"
--      $ DupIn (Pair (Var "z1") (Var "z2")) (Var "y")
--      $ AppIn (Var "res") (BVar "plus", (Pair (Var "z1") (Var "z2")))
--      $ (Var "res")
--

--
