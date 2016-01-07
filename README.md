# Rever

[![Haskell](http://b.repl.ca/v1/language-agda-green.png)](http://wiki.portal.chalmers.se/agda/pmwiki.php)

***Try*** to build something in Agda.

## Under developing

* Reduction
  + [ ] Δ-redex
  + [ ] →Δ
  + [ ] →\*Δ
  + [ ] →pΔ
  + [ ] →p\*Δ
* oo-NF
  + [ ] Δ-NF
  + [ ] Δ-NHF
* Input Set
  + [ ] Λ  
  + [ ] γ
  + [ ] Γ
  + [ ] ΛI
  + [ ] Ξ
  + [ ] Var ∪ Λ-NF0

## Todo

+ [**Generalize**] `data Term` for exposing *HEAD* or presenting the result of *sequentialization* with..  
  + A: define `data TermWithHead = ... `
  + B: apply the legendary *one-hole context* for `data TermZipper`
+ [**Generalize**] variable type - *Text*? *Integer*?
+ [**Implment**] encoding systems
  + *Church* encoding
  + *Scott* encoding
  + *Church-Scott* encoding
  + generalization..?!
+ [**Implment**] SKI combinators
+ [**Implment**] recursion via Y combinator
+ [**Implment**] operational semantics
+ [**Extend**] Polynomial functors as data structures
+ [**Extend**] speedup
  + native type as primitive, i.e. `∀ a . Lit a ∈ Λ+`
  + native function as primitive, i.e. `Fun (f :: F a -> G a) ∈ Λ+` where F, G are functors
+ [**Extend**] weak-, aka lazy-, evaluation  
+ [**Fantasy**] Type system (SystemF???)
