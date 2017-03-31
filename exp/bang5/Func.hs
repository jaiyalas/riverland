module Func where
--
import Expr
import Types
--
{- ###################################
        Predefined functions
################################### -}
prelude :: Expr -> Expr
prelude e = LetIn (mat "succ")   succExpr
          $ LetIn (mat "plus")   plusExpr
          $ LetIn (mat "plusR")  plusRExpr
          $ LetIn (mat "neg")    negExpr
        --   $ LetIn (mat "id")     (Lambda (mat "x") TypAny (Term $ var "x"))
          $ e
--

succExpr :: Expr
succExpr = Lambda (mat "#0") TypNat $
    Match (var "#0")
        [ -- (Lit $ N Z)  :~>
          (NatZ)  :~>
            (Term $ Lit $ N (S Z))
        , (NatS $ mat "u") :~>
            AppIn (mat "u2") ("succ", var "u")
                (Term $ NatS $ var "u2")
        ]
plusExpr :: Expr
plusExpr = Lambda (mat "#0") (TypProd TypNat TypNat) $
    LetIn (Prod (mat "_x") (mat "_y")) (Term $ var "#0") $
    Match (var "_y")
        [ -- (Lit (N Z))  :~>
          (NatZ)  :~>
            DupIn (Prod (mat "a") (mat "b")) (var "_x")
                (Term $ Prod (var "a") (var "b"))
        , (NatS $ mat "u") :~>
            AppIn (Prod (mat "x2") (mat "u2"))
                ("plus", Prod (var "_x") (var "u"))
                (Term $ Prod (var "x2") (NatS $ var "u2"))
        ]
plusRExpr :: Expr
plusRExpr = Lambda (mat "#0") (TypProd TypNat TypNat) $
    MatEq (var "#0")
        ((mat "x")  :~> (Term $ Prod (var "x") (Lit $ N Z)))
        ((Prod (mat "x") (NatS (mat "u"))) :~>
            (AppIn (Prod (mat "x2") (mat "u2"))
                ("plusR", Prod (var "x") (var "u"))
                (Term $ Prod (var "x2") (NatS $ var "u2"))))
negExpr :: Expr
negExpr = Lambda (mat "#0") TypBool $
    Match (var "#0")
        [ (Lit (B True))  :~>
            (Term $ Lit $ B False)
        , (Lit (B False)) :~>
            (Term $ Lit $ B True)
        ]
--
