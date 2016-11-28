module Term where
--

data Term = Var VName
          | Pair Term Term
          | NF
--
data Pattern = NF
             | Mat MName
             | NF
--
data FTerm = FTerm Fun Term
           | Lift Term
--
data Case = Case Pattern Term
data Cases = Nil Case | Cons Case Cases
data EqCase = (MName, Expr), (Pair ,Expr)
--
