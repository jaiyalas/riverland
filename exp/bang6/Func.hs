module Func where
--
import Expr
import Types
--
prelude :: Expr -> Expr
prelude e = succExpr e
--
succExpr :: Expr -> Expr
succExpr next = RecIn (BVar "succ")
    ( Lam "#0" TNat
        (Match (Var "#0")
            [ Lit (N Z) :~> Lit (N (S Z))
            , Suc (Var "u") :~>
                appRTo ("succ", "u") "u2" (Suc $ Var "u2")
            ])
        TNat
    ) next



--
appTo :: (VName, VName) -> VName -> Expr -> Expr
appTo (f, x) y e = AppIn (Var y) (Var f, Var x) e
--
appRTo :: (VName, VName) -> VName -> Expr -> Expr
appRTo (f, x) y e = AppIn (Var y) (BVar f, Var x) e
--
