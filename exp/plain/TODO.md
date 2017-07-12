# todo

+ [ ] local function and global function
+ [ ] bang!
+ [ ] flatten term-structure (back to old school)
    + [ ] 換掉 NatS / NatZ by new meta-constructor(?)
    + [ ] merge `term` into `Expr`
+ [ ] adding types info into Expr level
    + [ ] add function types
    + [x] add parameter type for lambda
+ [ ] ctx split or used label
    + maybe both of them will be needed
        + split for ctx of linear logic
        + label for indexing type (ant thus can be expended further)
+ [ ] type checking with ctx split and check
+ [ ] LetIn and RecIn again - avoid type inference of recursion
+ [ ] add Except Monad

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
