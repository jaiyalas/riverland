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
    | UnknownError
    deriving (Show, Eq)
--





data TypeError
    = TypeError Expr Typ Typ
    | ValueTypeUnknown Val
    | NotAFunctionType Expr Typ
    | TypeInconsist Typ Typ
    | MatchInconsist [Typ]
    deriving (Show, Eq)
--
-- instance Show TypeError where
--     show (TypeError e it ot) =
--         "["++ (show e) ++"]: "++(show it)++" does not match "++(show ot)
--     show (ValueTypeUnknown v) = "Value "++(show v)++" has unknown type."
--     show (NotAFunctionType e t) = "Expression "++(show e)++" has type "
--         ++(show t)++" which is not a function"
--
data CtxError
    = CtxExhausted CtxSwitch VName
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
    | NotAVariable Expr
    | NotAPair Expr
    | UnknownSyntaxError Expr
    deriving (Show, Eq)
--
data MatchError
    = Illegal Val Expr
    | Simple Val Expr
    | Exhausted
    deriving (Show, Eq)
