import LeanTyping.Utils
import LeanTyping.Syntax
import LeanTyping.Basic
import LeanTyping.Closure

namespace Typing.Untyped
open Typing.Untyped

partial def Term.fresh (used: List Ident) (id: Ident) : Ident :=
  if id ∈ used then Term.fresh used id.next else id

inductive Neutral V where
| nvar (v: Ident)
| napp (op: Neutral V) (arg: V)

def Neutral.toString (toString: V -> String) : Neutral V -> String
| .nvar v => s!"{v}"
| .napp op arg => s!"({op.toString toString} {toString arg})"

instance [ToString V] : ToString (Neutral V) where toString := Neutral.toString ToString.toString

inductive Value where
| clo (cl: Closure.Generic Term Value)
| neutral (neutral: Neutral Value)

instance : Coe (Neutral Value) Value where coe := fun n => .neutral n
instance : Coe (Closure.Generic Term Value) Value where coe := fun c => .clo c

partial def Value.toString : Value -> String
| .clo cl => cl.toString Value.toString
| neutral n => n.toString Value.toString
instance : ToString Value where toString := Value.toString

abbrev NeutralClosure := Closure.Generic Term Value

mutual
partial def Term.valNorm : Closure.Env Value -> Term -> Except String Value := fun ρ term =>
  match term with
  | .lam x b => pure $ .clo ⟨ρ, x, b⟩
  | .var x =>
     if let .some xv := ρ.assoc x
     then .ok xv
     else .error s!"Unknown variable {x}"
  | .app f arg => do
    let f <- f.valNorm ρ
    let arg <- arg.valNorm ρ
    f.app arg

partial def Value.app (f: Value) (arg: Value) : Except String Value :=
  match f with
  | .clo ⟨ρ,x,b⟩ => b.valNorm (ρ.cons (x,arg))
  | .neutral f => .ok (.neutral (.napp f arg))
  
end     

partial def Value.readBack (usedNames: List Ident) (vl: Value) : Except String Term :=
  match vl with
  | .clo ⟨ρ, x, body⟩ => do
     let y := Term.fresh usedNames x
     let neutralY := .neutral (.nvar y)
     let body <- body.valNorm (ρ.cons (x, neutralY))
     let body <- body.readBack (usedNames.cons y)
     pure $ .lam y body 
  | .neutral (.nvar x) => pure $ .var x
  | .neutral (.napp f arg) => do
     let f <- (f: Value).readBack usedNames
     let arg <- (arg: Value).readBack usedNames
     pure $ .app f arg

def Term.norm? (ρ: Closure.Env Value) : Term -> Except String Term :=
  fun v => do
     let v <- v.valNorm ρ
     v.readBack []
def Term.norm (ρ : Closure.Env Value) (t: Term) : Term :=
  match t.norm? ρ with
  | .ok res => res
  | .error _ => t
   
def Term.runProgramNorm (ρ: Closure.Env Value) (exprs: List Statement) : IO Unit := do
  let liftExceptIO {A} (e: Except String A) : IO A := liftExcept $ e.mapError IO.Error.userError
  let _ <- exprs.foldlM (init:= ρ) (fun env stmt => do
  match stmt with
  | .eval vl => do
     let res <- liftExceptIO $ vl.norm? env
     println! "{vl} ==> {res}"
     pure env
  | .define id vl =>
     let res <- liftExceptIO $ vl.valNorm env
     pure (env.cons (id, res))
  )
  return

#eval Term.runProgramNorm []
 (program:
    def id := (λ x . x)
    id id
    def f := (λ x . λ y . y x)
    (λ x . λ y . x y) (λ x . x)
    )

