module Types where
--
data Typ = TNat
         | TBool
         | TProd Typ Typ
         | TFunc Typ Typ
         deriving (Show, Eq)
--
data TypError = TypMismatch {srcNameTyp :: String, inTyp :: Typ, onTyp :: Typ}
--
instance Show TypError where
    show tmm = "["++(srcNameTyp tmm)++"]: "++
                (show $ inTyp tmm)++
                " does not match "++
                (show $ onTyp tmm)
