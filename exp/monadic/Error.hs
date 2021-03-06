module Error where
import Types
import Expr
import Ctx

--

-- CtxInternalError





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
data CtxError
    = CtxExhausted CtxSwitch VName
    | CtxSplitNotFound
    | UnknownCtxError
    | CtxSplitError VName
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
--
