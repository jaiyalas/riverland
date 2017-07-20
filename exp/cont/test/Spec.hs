module Main where
--
import Control.Monad.Reader
import Test.Hspec
import Cont
import Free
--
main :: IO ()
main = do
    tAppAbs
    tFree
    -- testEnvUniqueness
--
tAppAbs :: IO ()
tAppAbs = hspec $ do
    describe "[APPLICATION]" $ do
        it "[test2] \"App\" lambda function " $
            run test2 `shouldBe` (N 5)
        it "[test2\'] \"App\" function in linear enviroment" $
            run test2' `shouldBe` (N 5)
        it "[test2 == test2\']" $
            run test2 `shouldBe` run test2'
        it "[test3] \"App\" function in normal enviroment" $
            run test3 `shouldBe` (N 6)
        it "[test4] \"AppIn\" function in normal enviroment" $
            run test4 `shouldBe` (Pr (N 5) (N 55))
        it "[test5] \"AppIn\" lambda function" $
            run test5 `shouldBe` (N 9)
tFree :: IO ()
tFree = hspec $ do
    describe "[Free/Split]" $ do
        it "..." $
            splitEnv ["a","b"] env0 `shouldBe` ([("c",3)],[("a",1), ("b",2)])


env0 = zipWith (\a b -> ([a],b)) "abc" [1..3]
env1 = zipWith (\a b -> ('!':[a],b)) "abc" [1..3]
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
