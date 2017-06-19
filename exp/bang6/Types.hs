module Types where
--
data Typ = TNat
         | TBool
         | TProd Typ Typ
         | TFunc Typ Typ
         | TUnknown -- error msg only
         deriving (Show, Eq)
--
