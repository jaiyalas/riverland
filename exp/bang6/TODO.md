# todo

+ [ ] remove tyOut from Lam
    + failed -- QQ
+ [x] split for ctx of linear logic
    + [Ctx.hs]
        + [x] `popout :: VName -> Ctx -> Except SomeError (Val, Ctx)`
        + [x] `splitCtx :: [VName] -> [VName] -> Ctx -> Except SomeError (Ctx, Ctx)`
    + [Expr.hs]
        + [x] `freeVar :: Expr -> [VName]`
+ [x] type checking with ctx split and check
+ [ ] re-implement except/error
+ [ ] rval
+ [ ] translator for Expr to BiGuL(?)
+ [ ] used label (rather than dual-env)
    + label for indexing type (ant thus can be expended further)
+ [x] simple type checking
+ [x] LetIn and RecIn again - avoid type inference of recursion
+ [x] add Except Monad
+ [x] add Reader Monad
+ [x] local function and global function
+ [x] bang!
+ [x] flatten term-structure (back to old school)
    + [x] 換掉 NatS / NatZ by new meta-constructor(?)
    + [x] merge `term` into `Expr`
+ [x] adding types info into Expr level
    + [x] add function types
    + [x] add parameter type for lambda

## minor

+ [ ] FApp = (FunName, VTerm) 改成 FunName -> VTerm
+ [ ] DupIn {MTerm VTerm Expr} 改成 DupIn {MTerm Expr Expr}

## challenges

+ [ ] branching
    + at some point, the branching will be a problem due to the present of linearity
+ [ ] Higher-order function
    + the aim is to add HOF somehow but local function will be a tricky problem

## done

### bang5

+ [X] 合併 LetIn / RecIn
+ [x] 新增 Application (from LetIn)
+ [x] 增加 type terms
+ [x] Env/Ctx 重新設計製作 -- Reader
+ [x] 拿掉 TyBool
