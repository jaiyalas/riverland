module Typing where
--
import Types
import Ctx
import CtxOpT
import Expr

check :: Ctx Var Typ -> Expr -> Typ
check ctx (Term vt) = typeOfTerm ctx vt
check ctx (Pair e1 e2) = (check ctx e1) `times` (check ctx e2) -- env = env1 ++ env2
check ctx (Lambda mt ty e) = TypFunc ty (check (insertT Linear ctx mt ty) e)
-- --
check ctx (AppIn mt (fname, vt) next) =
    -- subsT Linear
check ctx (LetIn mt e next) =
    check (inserT Linear mt (check ctx e)) next
check ctx (DupIn mt vt next) = undefined

-- --
check ctx (Match vt []) = undefined
check ctx (Match vt (p :~> next : cs)) = undefined
check ctx (MatEq vt c1 c2) = undefined

typeOfTerm :: Ctx Var Typ -> VTerm -> Typ
typeOfTerm ctx (Lit val) = typeOf val
typeOfTerm ctx (Atom a) = lookupCtx Linear ctx a
typeOfTerm ctx (Prod t1 t2) =
    (typeOfTerm ctx t1) `times` (typeOfTerm ctx t2)
--
typeOfTerm ctx (NatS ta) = TypNat
typeOfTerm ctx NatZ = TypNat
