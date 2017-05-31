module Func where
--
import Expr
import Types
--
prelude :: Expr -> Expr
prelude e = succExpr
          $ plusExpr
          $ e
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

plusExpr :: Expr -> Expr
plusExpr next = RecIn (BVar "plus")
    ( Lam "#0" (TProd TNat TNat)
        ( LetIn (pairVar "_x" "_y") (Var "#0") $
            Match (Var "_y")
            [ Lit (N Z) :~> dup (Var "_x")
            , Suc (Var "u") :~>
                ( LetIn (Var "#1") (pairVar "_x" "u") $
                    appRTo ("plus", "#1") "z" $
                    LetIn (pairVar "x2" "u2") (Var "z") $
                    Pair (Var "x2") (Suc (Var "u2"))
                )
            ] )
        (TProd TNat TNat)
    ) next


--
dup :: Expr -> Expr
dup e = DupIn (pairVar "a" "b") e (pairVar "a" "b")
--
pairVar :: VName -> VName -> Expr
pairVar v1 v2 = Pair (Var v1) (Var v2)
--
appTo :: (VName, VName) -> VName -> Expr -> Expr
appTo (f, x) y e = AppIn (Var y) (Var f, Var x) e
--
appRTo :: (VName, VName) -> VName -> Expr -> Expr
appRTo (f, x) y e = AppIn (Var y) (BVar f, Var x) e
--
