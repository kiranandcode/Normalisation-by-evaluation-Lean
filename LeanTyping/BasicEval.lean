import LeanTyping.Syntax
import LeanTyping.Basic
import LeanTyping.Closure

namespace Typing
open Typing.Untyped
open Closure Basic

mutual

partial def Closure.Basic.Closure.apply (clo: Closure Term) (arg: Closure Term) : Except String (Closure Term) :=
  clo.body.val (clo.env.cons (clo.var, arg))

partial def Untyped.Term.val (ρ : Env (Closure Term)) (e: Term) : Except String (Closure Term) := match e with
| .lam x body =>
  pure (Closure.make ρ x body)
| .var x =>
  if let .some vl := ρ.assoc x
  then pure vl
  else Except.error s!"Unknown variable {x}"
| .app f arg => do
   let f <- f.val ρ
   let arg <- arg.val ρ
   f.apply arg
end

   
def Untyped.Term.runProgram (ρ: Env (Closure Term)) (exprs: List Untyped.Statement) : IO Unit := do
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
