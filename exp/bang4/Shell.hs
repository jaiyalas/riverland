module Shell where
--
import Expr
import Env
import Func
import Pat
import Eval
import Rval2

run :: FunName -> Val -> Val -- (Val, Env)
run fname args = fst $ run_ fname args

run_ :: FunName -> Val -> (Val, Env)
run_ fname args = eval mempty $ prelude $
    LetIn (mat "res") (Right (fname, Lit args)) (Term $ var "res")

plus2 :: Val -> (Val, Env)
plus2 args = eval mempty $ prelude $
    LetIn (mat "res") (Right ("succ", Lit args)) $
    LetIn (mat "res2") (Right ("succ", var "res")) $
    Term $ var "res2"

rrun_ :: FunName -> Val -> Env
rrun_ fname arg = rval (arg, mempty) $
    prelude $
    LetIn (mat "res") (Right (fname, var "input")) $
    Term $ var "res"

rrun :: FunName -> Val -> Val
rrun fname arg = subs Linear (rrun_ fname arg) (var "input")



-- rval with non-empty env
-- "plus" (3, Let y = 5 in x + y)


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
