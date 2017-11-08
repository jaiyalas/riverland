# cont

## todo

+ [x] 用 `App` 取代 `AppIn`
+ [ ] 重寫成對的 matching <=> ratching
    + [ ] Term => EPath
    + [ ] 重寫 eval1 和 rval0 的 Match/MatEq
    + [ ] `ps <-- cases --> nexts -dss-> ends`
+ [ ] 建構 `DupIn` 和 `MatEq` 的雙向性
    + [ ] seems like I should remove MatEq; the way we should go is
            using types to guarantee the backwards-equality
+ [ ] 合併 `BangIn` 和 `RecIn`


## then

+ [ ] eval1 -> appK1 (defunctionalze)
+ [ ] adding ⊕ as sum (but we have Bool already)
+ type safety
    + [ ] weaken
    + [ ] substitution
    + [ ] contraction
    + [ ] preservation
    + [ ] progress
+ game semantics
    + [ ] ...?

## nope!

+ <del>adding & as selective product</del>

## ???

問題是

1. 什麼時候我們真的會用上 MatEq ?
2. MatEq 中的兩個 pattern within cases 是否都要是 irrefusable? say, `(Var "x")`1111
3. BiGUL 直接可以保證寫不出反向 DupIn 會不過的程式 i.e.  n <-dupin-> (n,i) 是不行的
4. 換句話說, 假設我們有 BiGUL, 可能就不需要 MatEq ...
