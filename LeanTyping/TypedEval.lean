import LeanTyping.Basic
import LeanTyping.Syntax
import LeanTyping.Closure

namespace Typing.Typed

inductive Ty where
| nat
| arrow (t1 t2: Ty)
deriving Repr, DecidableEq

def Ty.toString : Ty -> String
| .nat => "ℕ"
| .arrow .nat t2 => s!"ℕ → {t2.toString}"
| .arrow t1 t2 => s!"({t1.toString}) → {t2.toString}"
instance : ToString Ty where toString := Ty.toString
instance : Repr Ty where reprPrec := fun t _ => Std.ToFormat.format t.toString

partial def unexpandTy : Lean.TSyntax `term -> Lean.PrettyPrinter.UnexpandM (Lean.TSyntax `ty)
| `(term| Ty.nat) => `(ty| ℕ)
| `(term| Ty.arrow $t1 $t2) => do
   let t1 <- unexpandTy t1
   let t2 <- unexpandTy t2
   `(ty| ($t1 → $t2))
| `(term| type! $t:ty) => pure t
| `(term| $id:ident) => `(ty| $id:ident)
| _ => throw ()

@[app_unexpander Ty.nat]
def unexpandTy.nat : Lean.PrettyPrinter.Unexpander
| `($_) => `(type! ℕ)

@[app_unexpander Ty.arrow]
def unexpandTy.arrow : Lean.PrettyPrinter.Unexpander
| `(term| $t) => do
   let t <- unexpandTy t
   `(type! $t)


#check (type! (ℕ → ℕ) → (ℕ → ℕ))

inductive Term
| var (name: Ident)
| lam (x: Ident) (body: Term)
| app (f arg : Term)
| zero
| add1 (t: Term)
| rec_ (ty: Ty) (n b s : Term)
| the (t: Term) (ty: Ty)

def Term.toString : Term -> String
| .var s => s
| .lam x body => s!"λ {x} . {body.toString}"
| .app f (.app f1 x1) => s!"{f.toString} ({(Term.app f1 x1).toString})"
| .app (.var f) arg => s!"{f} {arg.toString}"
| .app (.lam x body) arg => s!"((λ {x} . {body.toString}) {arg.toString})"
| .app f arg => s!"{f.toString} {arg.toString}"
| .the t ty => s!"({t.toString} : {ty})"
| .zero => s!"0"
| .add1 t => s!"{t.toString}.+1"
| .rec_ ty n b s => s!"rec[{ty}] ({n.toString}) ({b.toString}) ({s.toString})"

instance : ToString Term where
  toString := Term.toString
instance : Repr Term where
  reprPrec := fun t _ => Std.ToFormat.format t.toString


#eval lambda! (λ x . x : ℕ)

mutual 
partial def Term.synth (env: Closure.Env Ty) (e: Term) : Except String Ty := do
  match e with
  | .the t ty =>
     let _ <- t.check env ty
     return ty
  | .rec_ ty target base step =>
      let targetT <- target.synth env
      if targetT != .nat then
         throw s!"Expected Nat, got {targetT}"
      let _ <- base.check env ty
      let _ <- step.check env (type! ℕ → ty → ty)
      return ty
  | .var x =>
    let .some v <- pure (env.assoc x) | throw s!"Variable {x} not found"
    return v
  | .app f arg =>
     let fTy <- f.synth env
     let .arrow a b := fTy | throw s!"Not a function type: {fTy}"
     let _ <- arg.check env a
     return b
  | _ => throw s!"Attempted to synthesise type for unsupported expression: {e}"
     

partial def Term.check (env: Closure.Env Ty) (e: Term) (t: Ty) : Except String Unit := do
  match e with
  | .zero => return
  | .add1 n =>
     let _ <- n.check env .nat
     return
  | .lam x body =>
     let .arrow a b := t | throw s!"Instead of → type, got {t}"
     check (env.cons (x, a)) body b
  | _ =>
     let t2 <- synth env e
     if t != t2 then
        throw s!"Synthesised type {t2} when {t} was expected"
   
end
  
#eval (lambda! x).synth [("x",.nat)]
