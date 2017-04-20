module Types where
--
data Typ = TNat
         | TBool
         | TProd Typ Typ
         | TFunc Typ Typ
         deriving (Show, Eq)

data TypError = TypMismatch {srcNameTyp :: String, inTyp :: Typ, onTyp :: Typ}

instance Show TypError where
    show tmm = "["++(srcNameTyp tmm)++"]: "++
                (show $ inTyp tmm)++
                " does not match "++
                (show $ onTyp tmm)

-- class Product a where
--     times :: a -> a -> a
--     piL :: a -> Maybe a
--     piR :: a -> Maybe a
--
-- instance Product Typ where
--     times = TypProd
--     piL (TypProd tl _) = Just tl
--     piL _ = Nothing
--     piR (TypProd _ tr) = Just tr
--     piR _ = Nothing
