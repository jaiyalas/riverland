module Prelude where
--
import Expr
import Env
--
{- ###################################
        Predefined functions
################################### -}
prelude :: Expr -> Expr
prelude e = RecIn (mat "succ")   succExpr
          $ RecIn (mat "plus")   plusExpr
          $ RecIn (mat "plusR")  plusRExpr
          $ RecIn (mat "neg")    negExpr
          $ LetIn (mat "id")     (Left $ Lambda (mat "x") (Term $ var "x"))
          $ e
--

succExpr :: Expr
succExpr = Lambda (mat "#0") $
    Match (var "#0")
        [ -- (Lit $ N Z)  :~>
          (NatZ)  :~>
            (Term $ Lit $ N (S Z))
        , (NatS $ mat "u") :~>
            LetIn (mat "u2")
                (Right ("succ", var "u"))
                (Term $ NatS $ var "u2")
        ]
plusExpr :: Expr
plusExpr = Lambda (mat "#0") $
    LetIn (Prod (mat "_x") (mat "_y")) (Left $ Term $ var "#0") $
    Match (var "_y")
        [ -- (Lit (N Z))  :~>
          (NatZ)  :~>
            DupIn (Prod (mat "a") (mat "b")) (var "_x")
                (Term $ Prod (var "a") (var "b"))
        , (NatS $ mat "u") :~>
            LetIn (Prod (mat "x2") (mat "u2"))
                (Right ("plus", Prod (var "_x") (var "u")))
                (Term $ Prod (var "x2") (NatS $ var "u2"))
        ]
plusRExpr :: Expr
plusRExpr = Lambda (mat "#0") $
    MatEq (var "#0")
        ((mat "x")  :~> (Term $ Prod (var "x") (Lit $ N Z)))
        ((Prod (mat "x") (NatS (mat "u"))) :~>
            (LetIn (Prod (mat "x2") (mat "u2"))
                (Right ("plusR", Prod (var "x") (var "u")))
                (Term $ Prod (var "x2") (NatS $ var "u2"))))
negExpr :: Expr
negExpr = Lambda (mat "#0") $
    Match (var "#0")
        [ (Lit (B True))  :~>
            (Term $ Lit $ B False)
        , (Lit (B False)) :~>
            (Term $ Lit $ B True)
        ]
--
