module Eval where
--
import Data.List (find)
import Data.Maybe (fromJust)
import Data.Bifunctor
import Control.Monad.Reader
--
import Expr
--

--
eval1 :: Term -> Cont -> Compt Val
eval1 (Lit v) k = k $ return v
eval1 (Var name) k =
    k $ asks (fromJust . peekByKey name . {-traceShowId .-} snd)
eval1 (BVar name) k =
    k $ asks (fromJust . peekByKey name . fst)
eval1 (Succ t) k =
    eval1 t  (>>= \(N n) ->
        k $ return $ N $ (n + 1)
    )
eval1 (Pair t1 t2) k =
    eval1 t1 (>>= \v1 ->
        eval1 t2 (>>= \v2 ->
            k $ return $ Pr v1 v2
        )
    )
eval1 (Abs name tyIn func tyOut) k =
    k $ asks (Clos name tyIn func tyOut)

-- ##
eval1 (App (funT, argT)) k = do
    (Clos pname tyIn fbody tyOut localEnv) <- eval1 funT id
    argv <- eval1 argT id
    k $ local (const $ (pname, argv) `consL` localEnv) (eval1 fbody id)
-- ##
-- eval1 (App (funT, argT)) k = do
--     (Clos pname tyIn fbody tyOut localEnv) <- eval1 funT id
--     argv <- eval1 argT id
--     local (const $ (pname, argv) `consL` localEnv) (eval1 fbody k)
-- ##
-- eval1 (App (funT, argT)) k =
--     eval1 funT (>>= \(Clos pname tyIn fbody tyOut localEnv) ->
--         eval1 argT (>>= \argv ->
--             local (const $ (pname, argv) `consL` localEnv) (eval1 fbody k)
--         )
--     )
--
eval1 (LetIn (Var name) t next) k =
    eval1 t (>>= \v ->
        local (consL (name, v)) (eval1 next k)
    )
eval1 (LetIn (Pair t1 t2) t next) k =
    eval1 t (>>= \(Pr v1 v2) ->
        eval1 (LetIn t1 (Lit v1) $ LetIn t2 (Lit v2) next) k
    )
--
eval1 (RecIn (BVar name) t next) k =
    eval1 t (>>= \(Clos pname tyIn fbody tyOut localEnv) ->
        let funR = Clos pname tyIn fbody tyOut ((name, funR) `consN` localEnv)
        in local (consN (name, funR)) (eval1 next k)
    )
eval1 (BanIn (BVar name) t next) k =
    eval1 t (>>= \v ->
        local (consN (name, v)) (eval1 next k)
    )
eval1 (DupIn (Pair (Var name1) (Var name2)) t next) k =
    eval1 t (>>= \v ->
        eval1 (LetIn (Var name1) (Lit v) $ LetIn (Var name2) (Lit v) next) k
    )
--
eval1 (AppIn var (funT, argT) next) k =
    eval1 (LetIn var (App (funT, argT)) next) k
-- eval1 (AppIn (Var name) (Abs pname tyIn func tyOut, argT) next) k =
--     eval1 argT (>>= \argv ->
--         local (consL (pname, argv)) (eval1 func (>>= \resv ->
--             local (consL (name, resv)) (eval1 next k))
--         )
--     )
-- ##
-- eval1 (AppIn (Var name) (funT, argT) next) k = do
--     (Clos pname tyIn fbody tyOut localEnv) <- eval1 funT id
--     argv <- eval1 argT id
--     resv <- local (const $ (pname, argv) `consL` localEnv) (eval1 fbody id)
--     local (consL (name, resv)) (eval1 next k)
-- ## cannot restore env in the last local-invoking
-- eval1 (AppIn (Var name) (funT, argT) next) k =
--     eval1 funT (>>= \(Clos pname tyIn fbody tyOut localEnv) ->
--         eval1 argT (>>= \argv ->
--             local (const $ (pname, argv) `consL` localEnv) (eval1 fbody (>>= \resv ->
--                 local (consL (name, resv)) (eval1 next k))
--             )
--         )
--     )
--
eval1 (Match vt cs) k =
    eval1 vt (>>= \v ->
        let ((nns, nls), next) = fromJust $ findMatched v cs
        in local (bimap (nns +>+) (nls +>+)) (eval1 next k)
    )
eval1 (MatEq vt caseEq caseNEq) k =
    eval1 vt (>>= \(Pr v1 v2) ->
        if v1 == v2
            then eval1 (Match (Lit v1) [caseEq]) k
            else eval1 (Match (Pair (Lit v1) (Lit v2)) [caseNEq]) k
    )
--















--
matching :: Val -> Term -> Maybe (DualEnv Val)
matching v (Var vname) =
    return $ (vname, v) `consL` mempty
matching v (BVar vname) =
    return $ (vname, v) `consN` mempty
matching (N n1) (Lit (N n2)) = if n1 == n2
    then return mempty
    else Nothing
matching (B b1) (Lit (B b2)) = if b1 == b2
    then return mempty
    else Nothing
matching (N 0) (Succ e) = Nothing
matching (N n1) (Succ e) = matching (N (n1 - 1)) e
matching (Pr v1 v2) (Pair e1 e2) = do
    env1 <- matching v1 e1
    env2 <- matching v2 e2
    return $ env1 `mappend` env2
matching v e = Nothing
--
findMatched :: Val -> [Case] -> Maybe (DualEnv Val, Term)
findMatched v (mat :~> next : cs) =
    maybe (findMatched v cs) (\ctx -> return (ctx, next)) $ matching v mat
findMatched v [] = Nothing
--
