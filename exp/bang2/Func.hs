module Func where
--
import Expr
import Env
--

instance Monoid Env where
    mempty = Env [] prelude
    mappend (Env xs ys) (Env xs2 ys2) =
        Env (xs +>+ xs2) (ys +>+ ys2)

{- ###################################

        Predefined functions

################################### -}
prelude :: Ctx
prelude = [ (Var "succ"  , Closure succExpr)
          , (Var "plus"  , Closure plusExpr)
          , (Var "plusR" , Closure plusRExpr)
          , (Var "neg"   , Closure negExpr)
          ]


succExpr :: Expr
succExpr =
    Match (var "#0")
        [ (Lit $ N Z)  :~>
            (Term $ Lit $ N (S Z))
        , (NatS $ mat "u") :~> -- (S u)
            LetIn (mat "u2")
                (Right ("succ", var "u"))
                (Term $ NatS $ var "u2")
        ]
plusExpr :: Expr
plusExpr =
    LetIn (Prod (mat "_x") (mat "_y")) (Left $ var "#0") $
    Match (var "_y")
        [ (Lit (N Z))  :~>
            DupIn (Prod (mat "a") (mat "b")) (var "_x")
                (Term $ Prod (var "a") (var "b"))
        , (NatS $ mat "u") :~>
            LetIn (Prod (mat "x2") (mat "u2"))
                (Right ("plus", Prod (var "_x") (var "u")))
                (Term $ Prod (var "x2") (NatS $ var "u2"))
        ]
plusRExpr :: Expr
plusRExpr =
    MatEq (var "#0")
        ((mat "x")  :~> (Term $ Prod (var "x") (Lit $ N Z)))
        ((Prod (mat "x") (NatS (mat "u"))) :~>
            (LetIn (Prod (mat "x2") (mat "u2"))
                (Right ("plusR", Prod (var "x") (var "u")))
                (Term $ Prod (var "x2") (NatS $ var "u2"))))
negExpr :: Expr
negExpr =
    Match (var "#0")
        [ (Lit (B True))  :~>
            (Term $ Lit $ B False)
        , (Lit (B False)) :~>
            (Term $ Lit $ B True)
        ]
--
