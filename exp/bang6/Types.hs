module Types where
--
data Typ = TNat
         | TBool
         | TProd Typ Typ
         | TFunc Typ Typ
         deriving (Show, Eq)
--
