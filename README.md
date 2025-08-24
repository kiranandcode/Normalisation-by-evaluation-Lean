# lean-typing

Experiments with converting the Bidirectional typing through normalisation blog post into Lean.

```lean4

open Typing.Untyped in
#eval Term.runProgramNorm []
 (program:
    def id := (λ x . x)
    id id
    def f := (λ x . λ y . y x)
    (λ x . λ y . x y) (λ x . x))

-- 20:0:
-- id id ==> λ x . x
-- ((λ x . λ y . x y) λ x . x) ==> λ y . y


open Typing.Typed in
#eval Term.runProgram []
 (program:
    def id := (λ x . x)
    id id
    def f := (λ x . λ y . y x)
    (λ x . λ y . x y) (λ x . x))

-- 28:0:
-- id id ==> clo( ⊢ λ x . x)
-- ((λ x . λ y . x y) λ x . x) ==> clo(x : (clo(f : (clo(id : (clo( ⊢ λ x . x)) ⊢ λ x . λ y . y x)), id : (clo( ⊢ λ x . x)) ⊢ λ x . x)), f : (clo(id : (clo( ⊢ λ x . x)) ⊢ λ x . λ y . y x)), id : (clo( ⊢ λ x . x)) ⊢ λ y . x y)



```
