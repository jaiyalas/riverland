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
findFun fn [] = error $ "there is no such function: " ++ fn
findFun fn (fs:fss)
    | fn == fname fs = fs
    | otherwise = findFun fn fss
--
type FSpace = [FSpec]
--
globalFuns :: FSpace
globalFuns =
       [ FSpec "succ" [Mat "#0"] succExpr
       , FSpec "plus" [Mat "#0", Mat "#1"] plusExpr
       , FSpec "plusR" [Mat "#0"] plusRExpr
       , FSpec "neg" [Mat "#0"] negExpr
       , FSpec "and" [Mat "#0", Mat "#1"] andExpr
       ]
--
succExpr :: Expr
succExpr =
    Match (var "#0")
        [ (Lit $ N Z)  :-->
            (Return $ Lit $ N (S Z))
        , (NatS $ mat "u") :-->
            LetIn (mat "u2")
                (Right ("succ", [var "u"]))
                (Return $ NatS $ var "u2")
        ]
plusExpr :: Expr
plusExpr =
    Match (var "#1")
        [ (Lit (N Z))  :-->
            DupIn (Prod (mat "a") (mat "b")) (var "#0")
                (Return $ Prod (var "a") (var "b"))
        , (NatS $ mat "u") :-->
            LetIn (Prod (mat "x2") (mat "u2"))
                (Right ("plus", [var "#0", var "u"]))
                (Return $ Prod (var "x2") (NatS $ var "u2"))
        ]
plusRExpr :: Expr
plusRExpr = LetIn (Prod (mat "#0_a") (mat "#0_b")) (Left $ var "#0") $
    MatEq (Prod (var "#0_a") (var "#0_b"))
        ((mat "x")  :--> (Term $ Prod (var "x") (Lit $ N Z)))
        ((Prod (mat "x") (NatS (mat "u"))) :-->
            (LetIn (Prod (mat "x2") (mat "u2"))
                (Right ("plusR", [Prod (var "x") (var "u")]))
                (Return $ Prod (var "x2") (NatS $ var "u2"))))
negExpr :: Expr
negExpr =
    Match (var "#0")
        [ (Lit (B True))  :-->
            (Return $ Lit $ B False)
        , (Lit (B False)) :-->
            (Return $ Lit $ B True)
        ]
andExpr :: Expr
andExpr = undefined
--

--
