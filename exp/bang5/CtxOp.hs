module CtxOp where
--
import Types
import Ctx
import Expr
--

-- 是擅長假裝自己是 Val 的朋友呢
class FromVal a where
    fromVal :: Val -> a
instance FromVal Val where
    fromVal = id
instance FromVal (Term a) where
    fromVal = Lit
instance FromVal Expr where
    fromVal = Term . Lit
instance FromVal Typ where
    fromVal (N _) = TypNat
    fromVal (Pr v1 v2) = (fromVal v1) `times` (fromVal v2)
    fromVal _ = error "oops"

-- 是擅長 +1/-1 的朋友呢
class Natable a where
    succUni :: a -> a
    predUni :: a -> a
instance Natable Typ where
    succUni = id
    predUni = id
instance Natable Val where
    succUni (N nat) = N $ S nat
    succUni x = x
    predUni (N (S nat)) = N nat
    predUni (N Z) = error "N Z cannot be \"pred\"ed"
    predUni x = x
instance Natable (Term a) where
    succUni (Lit val) = Lit (succUni val)
    succUni (NatS t) = NatS (succUni t)
    succUni NatZ = NatS NatZ
    succUni (Atom a) = Atom a
    succUni (Prod t1 t2) = Prod (succUni t1) (succUni t2)
    predUni (Lit val) = Lit (predUni val)
    predUni (NatS t) = NatS (predUni t)
    predUni NatZ = error "N Z cannot be \"pred\"ed"
    predUni (Atom a) = Atom a
    predUni (Prod t1 t2) = Prod (predUni t1) (predUni t2)

-- variable substitution
subs :: (Product a, FromVal a, Natable a)
     => CtxSwitch -> VTerm -> Ctx Var a -> a 
subs _ (Lit val) ctx = fromVal val
subs ctxSW (Atom va) ctx = lookupCtx ctxSW ctx va
subs ctxSW (Prod vt1 vt2) ctx =
    (subs ctxSW vt1 ctx) `times` (subs ctxSW vt2 ctx)
subs ctxSW (NatS vt) ctx = succUni $ subs ctxSW vt ctx
subs ctxSW (NatZ) ctx = fromVal (N Z)
--
--
-- matchable insertion
insert :: (Show a, Eq a, Product a, Natable a)
       => CtxSwitch -> MTerm -> a -> Ctx Var a -> Ctx Var a
insert _ (Lit _) _ ctx = ctx
insert ctxSW mt@(Atom (Mat name)) a ctx =
    insertCtx (\_ -> Var name) ctxSW (mt, a) ctx
insert ctxSW (Prod mt1 mt2) a ctx =
    case (piL a, piR a) of
        (Just v1, Just v2) ->
            insert ctxSW mt2 v2 $ insert ctxSW mt1 v1 ctx
        _ -> error $ "<< insert | Prod >>\n"++
            (show a) ++ "is not a Product"
insert ctxSW (NatS mt) a ctx = insert ctxSW mt (predUni a) ctx
-- NatZ included
insert ctxSW mt a ctx = error $
    "<< insert | Unknown >>\n"++
    "\tCannot insert \"" ++ (show mt) ++ "/" ++ (show a) ++
    "\" in "++(show ctxSW)++" context."
