module River where

type VName = String

data Expr = Var VName
          | Const Val
          | Suc Expr

          | Lam VName Expr
          | App Expr VName
          | Let VName Expr Expr

          | Pair Expr Expr

          | Dup Expr
          | Eq Expr Expr

          | MatchP VName (VName, VName) Expr
          | CaseN VName Expr VName Expr
  deriving (Show, Eq)

data Val = Num Int
         | Bol Bool
         | Tup Val Val
         | Fun Env VName Expr
  deriving (Show, Eq)

-- Environment

type Env = [(VName, Val)]

lookUp :: VName -> Env -> Val
lookUp x env = maybe err id $ lookup x env
  where err = error ("Variable " ++ x ++ " not found.")

-- Evaluation

eval :: Expr -> Env -> Val
eval (Var x) env = lookUp x env
eval (Const v) env = v
eval (Suc e) env =
  case eval e env of
    Num n -> Num (1+n)
    _ -> error "not a numer"

eval (Lam x body) env = Fun env x body
eval (App f y) env =
  case eval f env of
    Fun env' x body ->
       eval body ((x,lookUp y env) : env)
    _ -> error "not a function"
eval (Let x e1 e2) env =
   eval e2 ((x, eval e1 env) : env)

eval (Pair e1 e2) env =
  Tup (eval e1 env) (eval e2 env)
eval (Dup e) env =
   let v = eval e env in Tup v v
eval (Eq e1 e2) env =
   let (v1,v2) = (eval e1 env, eval e2 env)
   in if v1 == v2 then v1 else error "not equal"

eval (CaseN x e0 y e1) env =
   case lookUp x env of
     Num 0 -> eval e0 env
     Num n -> eval e1 ((y, Num (n-1)):env)
     _ -> error "not a number"
eval (MatchP x (x1,x2) e0) env =
   case lookUp x env of
     Tup v1 v2 -> eval e0 ((x1,v1):(x2,v2):env)
     _ -> error "not a pair"

plus :: Expr
plus = Lam "mn"
 (MatchP "mn" ("m", "n")
   (CaseN "m" (Pair (Var "n") (Const (Num 0)))
       "m1" (Let "m1n" (Pair (Var "m1") (Var "n"))
             (Let "p" (App (Var "plus") "m1n")
              (MatchP "p" ("m1+n", "m1'")
                (Pair (Suc (Var "m1+n")) (Suc (Var "m1'")))))
            )))

prelude :: Env
prelude = [("plus", eval plus prelude)]

tst :: Expr
tst = Let "mn" (Pair (Const (Num 3)) (Const (Num 5)))
        (App (Var "plus") "mn")

{-
*River> eval tst prelude
Tup (Num 8) (Num 3)
-}

{- Wish:
         reval e env v = env'
     <=> eval e (env' ++ env) = v
-}

reval :: Expr -> Env -> Val -> Env
reval (Var x) env v
  | Just v' <- lookup x env, v == v' = []
  | otherwise = [(x,v)]
reval (Const v') env v
  | v' == v = []
  | otherwise = error "constant not matching"
reval (Suc e) env (Num n) = reval e env (Num (n-1))
reval (Suc e) env _ = error "not a number"

reval (App (Var f) y) env v =
  case lookUp f env of
    Fun env' x body -> reval (App (Lam x body) y) env' v
reval (App (Lam x body) y) env v =
  mvEntry x y (reval body env v)

reval (Let x e1 e2) env v =
  let env' = reval e2 env v
      vx = lookUp x env'
      env'' = reval e1 env vx
  in env'' ++ rmEntry x env'

reval (Pair e1 e2) env (Tup v1 v2) =
  reval e1 env v1 ++ reval e2 env v2  -- shall we do some checks?
reval (Pair _ _) _ _ = error "not a pair"

reval (Dup e) env (Tup v1 v2)
  | v1 == v2 = reval e env v1
  | otherwise = error "duplicated values not equal"

reval (MatchP x (x1,x2) e) env v =
  let env' = reval e env v
      vx1 = lookUp x1 env'
      vx2 = lookUp x2 env'
  in (x, Tup vx1 vx2) : (rmEntry x2 . rmEntry x1 $ env')

reval (CaseN x e0 y e1) env v =
  case oracle (extractCon e0) (extractCon e1) v of
    Just False -> (x, Num 0) : reval e0 env v
    Just True ->
       let env' = reval e1 env v
           Num n = lookUp y env'
       in (x, Num (1+n)) : rmEntry y env'
    Nothing -> error "oracle failed"

extractCon :: Expr -> Expr
extractCon (Let x e1 e2) = extractCon e2
extractCon (MatchP x yz e) = extractCon e
extractCon (CaseN x e0 y e1) =
  error "extractCon does not yet deal with CaseN"
extractCon (App _ _) =
  error "constructor hidden in application"
extractCon e = e

oracle :: Expr -> Expr -> Val -> Maybe Bool
oracle (Const v1) _ v | v1 == v = Just False
oracle _ (Const v2) v | v2 == v = Just True
oracle (Suc e) (Const (Num 0)) (Num n) | n > 0 = Just False
oracle (Const (Num 0)) (Suc e) (Num n) | n > 0 = Just True
oracle (Suc e1) (Suc e2) v = oracle e1 e2 v
oracle (Pair e1 e2) (Pair d1 d2) (Tup v1 v2) =
  case oracle e1 d1 v1 of
    Just b  -> Just b
    Nothing -> oracle e2 d2 v2
oracle _ _ _ = Nothing

-- some more tests

tst1 :: Expr
tst1 = Let "x" (Suc (Var "y"))
        (Let "z" (Suc (Var "x"))
          (Suc (Suc (Var "z"))))
  {-
    *River> reval tst1 [] (Num 6)
    [("y",Num 2)]
  -}

tst2 :: Expr
tst2 = Pair (Suc (Var "x")) (Const (Num 0))
  {-  *River> reval tst2 [] (Tup (Num 7) (Num 0))
      [("x",Num 6)]
      *River> reval tst2 [] (Tup (Num 7) (Num 1))
      [("x",Num 6)*** Exception: constant not matching
  -}

tst3 :: Expr
tst3 = CaseN "m" (Pair (Var "n") (Const (Num 0)))
         "m1" (Pair (Suc (Var "m1")) (Suc (Var "m1'")))
{-
*River> reval tst3 [] (Tup (Num 4) (Num 0))
[("m",Num 0),("n",Num 4)]
*River> reval tst3 [] (Tup (Num 4) (Num 1))
[("m",Num 4),("m1'",Num 0)]
-}

{-
*River> reval (App (Var "plus") "mn") prelude (Tup (Num 8) (Num 3))
[("mn",Tup (Num 3) (Num 5))]
*River> reval (App (Var "plus") "mn") prelude (Tup (Num 12) (Num 3))
[("mn",Tup (Num 3) (Num 9))]
*River> reval (App (Var "plus") "mn") prelude (Tup (Num 12) (Num 7))
[("mn",Tup (Num 7) (Num 5))]

-}
-- environment management

mvEntry :: VName -> VName -> Env -> Env
mvEntry x y [] = []
mvEntry x y ((x',v) : xs)
   | x == x'   = (y,v) : xs
   | otherwise = (x',v) : mvEntry x y xs

rmEntry :: VName -> Env -> Env
rmEntry x [] = []
rmEntry x ((x',v) : xs)
   | x == x' = xs
   | otherwise = (x',v) : rmEntry x xs
