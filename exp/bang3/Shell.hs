module Shell where
--
import Expr
import Env
import Func
import Pat
import Eval
-- import Rval
--
runSucc :: Int -> (Val, Env)
runSucc n = eval mempty $ prelude $
    LetIn (mat "res") (Right ("succ", Lit $ N $ int2nat n)) (Term $ var "res")




tSucc :: Int -> (Val, Env)
tSucc m = eval ((Var "#0", N $ int2nat m) `consL` mempty) succExpr

-- tPlus :: (Int, Int) -> (Val, Env)
-- tPlus (m,n) = eval ((Var "#0", Pair (N $ int2nat m) (N $ int2nat n)) `consL` mempty) plusExpr
--
-- tPlusR :: (Int, Int) -> (Val, Env)
-- tPlusR (m,n) = eval
--     ((Var "#0", Pair (N $ int2nat m) (N $ int2nat n)) `consL` mempty) plusRExpr

sr :: (Val, Env) -> IO ()
sr (v, Env xs ys) = do
    putStr "Result: "
    putStrLn $ show v
    putStrLn $ "Env: " ++
        (show $ length xs) ++
        " / " ++
        (show $ length ys)
-- srr :: Env -> IO ()
-- srr env = sr $ raccess Linear env (Var "#0")
-- --
--
-- rSucc :: Int -> Env
-- rSucc n = rval ( N $ int2nat n, mempty) succExpr
-- --
-- rPlus :: (Int, Int) -> Env
-- rPlus (m, n) = rval ( Pair (N $ int2nat m) (N $ int2nat n)
--                      , mempty) plusExpr
