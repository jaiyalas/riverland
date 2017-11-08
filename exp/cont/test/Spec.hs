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
    tType
    tRval
    -- tFree
--
tAppAbs :: IO ()
tAppAbs = hspec $ do
    describe "[APPLICATION]" $ do
        it "[test1] \"App\" lambda function " $
            run test1 `shouldBe` (Pr (N 2) (N 5))
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
--
tType :: IO ()
tType = hspec $ do
    describe "[TYPE]" $ do
        it "[Type/LetIn]" $
            trun (LetIn (Var "x") (Lit $ N 1) (Var "x")) `shouldBe` TNat
        it "[Type/test1]" $
            trun test1 `shouldBe` TProd TNat TNat
        it "[Type/test2]" $
            trun test2 `shouldBe` TNat
        it "[Type/test2']" $
            trun test2' `shouldBe` TNat
        it "[Type/test3]" $
            trun test3 `shouldBe` TNat
        it "[Type/test4]" $
            trun test4 `shouldBe` TProd TNat TNat
        it "[Type/test5]" $
            trun test5 `shouldBe` TNat
--
tRval :: IO ()
tRval = hspec $ do
    describe "[RVAL]" $ do
        it "[RVAL/Simple]" $
            rrun (Var "x") (N 5) `shouldBe` ([], [("x",N 5)])
        it "[RVAL/Simple2]" $
            run testIdNat `shouldBe` (N 5)
        it "[RVAL/Simple3]" $
            -- appin (Var "out") (idNat, Lit $ N 5) (Var "out")
            rrun testIdNat (N 5) `shouldBe` mempty
--

--

--
run :: Term -> Val
run e = runReader (eval1 e id) ([], [])
--
trun :: Term -> Typ
trun e = runReader (typeof0 e) mempty
rrun :: Term -> Val -> (DualEnv Val)
rrun e v = runReader (rval0 v e) mempty

-- test = succExpr $ plusExpr
--      $ LetIn (Var "x") (Lit $ N 3)
--      $ appRTo ("succ", "x") "y"
--      $ DupIn (Pair (Var "z1") (Var "z2")) (Var "y")
--      $ AppIn (Var "res") (BVar "plus", (Pair (Var "z1") (Var "z2")))
--      $ (Var "res")
--
--
tFree :: IO ()
tFree = hspec $ do
    describe "[FREE]" $ do
        it "[Free/Split]" $
            splitEnv ["a","b"] env0 `shouldBe` ([("c",3)],[("a",1), ("b",2)])
env0 = zipWith (\a b -> ([a],b)) "abc" [1..3]
env1 = zipWith (\a b -> ('!':[a],b)) "abc" [1..3]

--
