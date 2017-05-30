module Error where
import Types
import Expr
import Ctx

--



data ErrorMsg
    = MismatchPatt MatchError
    | MismatchType TypeError
    | NotFound CtxError
    | MismatchSynt IllegalSyntax
    deriving (Show, Eq)
--
data TypeError = TypeError String Typ Typ deriving Eq
--
instance Show TypeError where
    show (TypeError nt it ot) =
        "["++ nt ++"]: "++(show it)++" does not match "++(show ot)
--
data CtxError
    = LinearCtxExhausted VName
    | NormalCtxExhausted VName
    | TotalExhausted VName
    | UnknownCtxError
    deriving Eq
instance Show CtxError where
    show (CtxExhausted cs v) =
        "[Environment "++(show cs)++" exhausted]: key "++
        (show v)++" cannot be found"
--
data IllegalSyntax
    = InvalidConstructor Expr
    | NotAFunction Expr
    deriving (Show, Eq)
--
data MatchError
    = Illegal Val Expr
    | Simple Val Expr
    | Exhausted
    deriving (Show, Eq)
