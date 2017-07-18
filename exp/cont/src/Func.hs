module Func where
--
import Expr
--

-- ###########
-- ## Sugar ##
-- ###########

appRTo :: (Name, Name) -> Name -> Term -> Term
appRTo (f, x) y e = AppIn (Var y) (BVar f, Var x) e
pairVar :: Name -> Name -> Term
pairVar v1 v2 = Pair (Var v1) (Var v2)
dupin :: Term -> Term
dupin e = DupIn (pairVar "a" "b") e (pairVar "a" "b")

-- #############
-- ## Prelude ##
-- #############

succExpr :: Term -> Term
succExpr next = RecIn (BVar "succ")
    ( Abs "#0" TNat
        (Match (Var "#0")
            [ Lit (N 0) :~> Lit (N 1)
            , Succ (Var "u") :~>
                appRTo ("succ", "u") "u2" (Succ $ Var "u2")
            ])
        TNat -- return type
    ) next
--
plusExpr :: Term -> Term
plusExpr next = RecIn (BVar "plus")
    ( Abs "#0" (TProd TNat TNat)
        ( LetIn (pairVar "_x" "_y") (Var "#0") $
            Match (Var "_y")
            [ Lit (N 0) :~> dupin (Var "_x")
            , Succ (Var "u") :~>
                ( LetIn (Var "#1") (pairVar "_x" "u") $
                    appRTo ("plus", "#1") "z" $
                    LetIn (pairVar "x2" "u2") (Var "z") $
                    Pair (Var "x2") (Succ (Var "u2"))
                )
            ] )
        (TProd TNat TNat) -- return type
    ) next
--
-- ##################
-- ## testing case ##
-- ##################

test1 :: Term
test1 = succExpr $ plusExpr
     $ LetIn (Var "x") (Lit $ N 1)
     $ LetIn (Var "y") (Lit $ N 2)
     $ AppIn (Var "z1") (BVar "succ", Var "x")
     $ AppIn (Var "z2") (BVar "succ", Var "y")
     $ AppIn (Var "r") (BVar "plus", Pair (Var "z1") (Var "z2"))
     $ (Var "r")
