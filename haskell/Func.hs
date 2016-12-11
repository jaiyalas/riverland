module Func where
--
import Expr
--
data FSpec = FSpec { fname :: FunName
                   , fargs :: [Mat]
                   , fbody :: Expr
                   }
           deriving (Show, Eq)
--
findFun :: FunName -> FSpace -> FSpec
findFun fn [] = error "there is no such function"
findFun fn (fs:fss)
    | fn == fname fs = fs
    | otherwise = findFun fn fss
--
type FSpace = [FSpec]
--
globalFuns :: FSpace
globalFuns =
       [ FSpec "Succ" [Mat "#0"] succExpr
       , FSpec "Plus" [Mat "#0", Mat "#1"] plusExpr
       , FSpec "Neg" [Mat "#0"] negExpr
       , FSpec "And" [Mat "#0", Mat "#1"] andExpr
       ]
--
succExpr :: Expr
succExpr =
    Match (var "#1")
        [ (Lit $ N Z)  :-->
            (Term $ Lit $ N (S Z))
        , (NatS $ mat "u") :-->
            LetIn (mat "u2")
                (Right ("succ", [var "u"]))
                (Term $ NatS $ var "u2")
        ]
plusExpr :: Expr
plusExpr =
    Match (var "#1")
        [ (Lit (N Z))  :-->
            DupIn (Prod (mat "a") (mat "b")) (var "#0")
                (Term $ Prod (var "a") (var "b")) -- !!! BUG
        , (NatS $ mat "u") :-->
            LetIn (Prod (mat "x2") (mat "u2"))
                (Right ("Plus", [var "#0", var "u"]))
                (Term $ Prod (var "x2") (var "u2"))
        ]
negExpr :: Expr
negExpr =
    Match (var "#0")
        [ (Lit (B True))  :-->
            (Term $ Lit $ B False)
        , (Lit (B False)) :-->
            (Term $ Lit $ B True)
        ]
andExpr :: Expr
andExpr = undefined
--

--
