module Shell where
--
import Expr
import Env
import Func
import Pat
import Eval

run :: FName -> Val -> (Val, Env)
run fname args = eval mempty $ prelude $
    LetIn (mat "res") (Right (fname, Lit args)) (Term $ var "res")

-- --
-- rrunSucc :: Int -> IO ()
-- rrunSucc n = print $ rval (N $ int2nat n, mempty) $
--     prelude $
--     LetIn (mat "res")
--         (Right ("succ", Lit $ N $ int2nat n))
--         (Term $ var "res")
--
--
-- rrunId n = rval (N $ int2nat n, mempty)
--     $ LetIn (mat "id")
--         (Left $
--             Lambda (mat "x") (Term $ var "x")
--         )
--     $ LetIn (mat "res")
--         (Right ("id", Lit $ N $ int2nat n))
--         (Term $ var "res")
--
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

{- ############### auxiliary ############### -}

int :: Int -> Val
int = N . int2nat

sr :: (Val, Env) -> IO ()
sr (v, Env xs ys) = do
    putStr "Result: "
    putStrLn $ show v
    putStrLn $ "Env: " ++
        (show xs) ++ "\n   | " ++ (show $ map fst ys)
