module Error where
import Typ
import Expr

--
data ErrorMsg
    = MismatchPatt MatchError
    | MismatchType TypeError
    deriving (Show, Eq)
--
data TypeError = TypeError String Typ Typ
--
instance Show TypError where
    show (TypeError nt it ot) =
        "["++ nt ++"]: "++(show it)++" does not match "++(show ot)
--
data MatchError
    = Illegal Expr Expr
    | Closure
    | Simple Expr Expr
    deriving (Show, Eq)
