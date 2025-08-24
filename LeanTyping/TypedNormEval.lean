import LeanTyping.Basic
import LeanTyping.Syntax
import LeanTyping.Closure
import LeanTyping.TypedEval

namespace Typing.Typed

namespace Value
inductive Generic (Neutral: Type) where
| zero
| add1 (pred: Generic Neutral)
| neu (ty: Ty) (neutral: Neutral)
| clo (cl: Closure.Generic Term (Generic Neutral))

partial def Generic.toString (NeutralToString: Neutral -> String) : Generic Neutral -> String
| zero => "0"
| add1 pred => s!"({pred.toString NeutralToString}).+1"
| neu ty nt => s!"neu({ty}, {NeutralToString nt})"
| clo cl =>
  let cl := Closure.Generic.toString (Generic.toString NeutralToString) cl
  s!"clo({cl})"

instance [ToString Neutral] : ToString (Generic Neutral) where
  toString := Generic.toString toString

structure Norm (Value: Type) where
  ty: Ty
  value: Value

def Norm.toString (ValueToString: Value -> String) : Norm Value -> String :=
  fun ⟨ty,vl⟩ => s!"⟨{ty},{ValueToString vl}⟩"

instance [ToString Value] : ToString (Norm Value) where
  toString := Norm.toString toString

end Value

inductive Neutral where
| var (name: Ident)
| app (f: Neutral) (arg: Value.Norm (Value.Generic Neutral))
| rec_ (ty: Ty) (target: Neutral) (base step: Value.Norm (Value.Generic Neutral))

partial def Neutral.toString : Neutral -> String
| var name => s!"{name}"
| app f arg =>
   s!"app({Neutral.toString f}, {normToString arg})"
| rec_ ty target base step =>
   s!"rec_({ty}, {Neutral.toString target}, {normToString base}, {normToString step})"
where normToString := Value.Norm.toString (Value.Generic.toString Neutral.toString)

instance : ToString Neutral where
  toString := Neutral.toString

instance : ToString (Value.Norm (Value.Generic Neutral)) where
  toString := Value.Norm.toString (Value.Generic.toString Neutral.toString)


abbrev Value := Value.Generic Neutral
abbrev Norm := Value.Norm Value
abbrev Closure := Closure.Generic Term Value

mutual
partial def Term.val (env: Closure.Env Value) (t: Term) : Except String Value := do
   match t with
   | .the t ty => t.val env
   | .zero => return .zero
   | .add1 n =>
      let n <- n.val env
      return .add1 n
   | .var x =>
      let .some vl := env.assoc x | throw s!"use of unknown variable {x}"
      return vl
   | .lam x b =>
      return .clo (Closure.Generic.mk env x b)
   | .rec_ ty target base step =>
      let target <- target.val env
      let base <- base.val env
      let step <- step.val env
      Term.doRec_ ty target base step
   | .app f arg =>
     let f <- f.val env
     let arg <- arg.val env
     f.apply arg

partial def Term.doRec_ (ty: Ty) (target: Value) (base: Value) (step: Value) : Except String Value := throw "not implemented"

partial def Value.apply (f: Value) (arg: Value) : Except String Value := do
   match f with
   | .clo ⟨env, x, e⟩ =>
     e.val (env.cons (x, arg))
   | .neu (.arrow a b) ne =>
      return .neu b (.app ne (.mk a arg))
   | _ => throw s!"invalid"

end



inductive Statement where | eval (t: Term) | define (name: Ident) (vl: Term)

def Statement.toString : Statement -> String
| .eval t => t.toString
| .define name vl => s!"def {name} := {vl.toString}"
instance : ToString Statement where toString := Statement.toString

def Term.runProgram (ρ: Closure.Env Value) (exprs: List Statement) : IO Unit := do
  let liftExceptIO {A} (e: Except String A) : IO A := liftExcept $ e.mapError IO.Error.userError
  let _ <- exprs.foldlM (init:= ρ) (fun env stmt => do
  match stmt with
  | .eval vl => do
     let res <- liftExceptIO $ vl.val env
     println! "{vl} ==> {res}"
     pure env
  | .define id vl =>
     let res <- liftExceptIO $ vl.val env
     pure (env.cons (id, res))
  )
  return

#eval Term.runProgram []
 (program:
    def id := (λ x . x)
    id id
    def f := (λ x . λ y . y x)
    f id
    )

