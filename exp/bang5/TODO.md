# todo

+ [ ] local function and global function
+ [ ] 最終還是需要 bang!
+ [ ] 增加 type terms
+ [ ] Env/Ctx 重新設計製作 -- Reader
+ [ ] 拿掉 TyBool
+ [ ] 補完 expr: sum
+ [ ] 換掉 NatS / NatZ by new meta-constructor(?)
+ [ ] adding types info into Expr level
+ [ ] ctx split or used label
    + maybe both of them will be needed
        + split for ctx of linear logic
        + label for indexing type (ant thus can be expended further)

## minor

+ [ ] FApp = (FunName, VTerm) 改成 FunName -> VTerm
+ [ ] DupIn {MTerm VTerm Expr} 改成 DupIn {MTerm Expr Expr}
+ [ ] 拿掉 MatEq

## challenges

+ [ ] branching
    + at some point, the branching will be a problem due to the present of linearity
+ [ ] Higher-order function
    + the aim is to add HOF somehow but local function will be a tricky problem

## done

### bang5

+ [X] 合併 LetIn / RecIn
+ [X] 新增 Application (from LetIn)
