# Riverland

Flowing as river; solid as land.

## TODO

### syntax

+ [ ] lambda abs/app
+ [x] isolated non-linear context
+ [x] function context
+ [x] update with name-conflit checking
+ [x] reversed program translator
+ [ ] get rid of MatEq
+ [ ] fixed-point (for recursion)

### bugs

+ [x] no need for GC/throwing used variable away (this should be prevented by type-checker)
+ [x] making name-conflict free (as we using env)
+ [x] require: `(let ... in ... , let ... in ...)` aka ...?
+ [x] closure needs env (ref: River)
+ [x] re-write/check Expr
+ [x] re-write/check Env
+ [x] re-write/check Func
+ [x] re-write/check Pat
+ [x] re-write/check Eval
+ [x] re-write/check Rval
+ [x] re-write/check Shell
+ [ ] `NatS`
    + [ ] get rid off it
    + [ ] add `NatZ` or something
+ [x] how to re-new function-space?
    + [x] LetInRec

### linear? typed

+ [ ] type term

### plus

+ [ ] non-determinism monad
+ [ ] maybe monad
+ [ ] state monad
+ [ ] monad zero
