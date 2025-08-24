import LeanTyping.Utils
import LeanTyping.Syntax


namespace Typing.Untyped

inductive Term
| var (name: Ident)
| lam (x: Ident) (body: Term)
| app (f arg : Term)

def Term.toString : Term -> String
| .var s => s
| .lam x body => s!"λ {x} . {body.toString}"
| .app f (.app f1 x1) => s!"{f.toString} ({(Term.app f1 x1).toString})"
| .app (.var f) arg => s!"{f} {arg.toString}"
| .app (.lam x body) arg => s!"((λ {x} . {body.toString}) {arg.toString})"
| .app f arg => s!"{f.toString} {arg.toString}"

instance : ToString Term where
  toString := Term.toString
instance : Repr Term where
  reprPrec := fun t _ => Std.ToFormat.format t.toString

@[app_unexpander Term.var]
def unexpandTermvar : Lean.PrettyPrinter.Unexpander
| `($_ $v:str) => let id := Lean.mkIdent (Lean.Name.mkStr1 v.getString)
   `(lambda! $id:ident)
| `($_ $v:ident) =>  `(lambda! $v:ident)
| _ =>
  throw ()

@[app_unexpander Typing.Untyped.Term.app]
def unexpandTermapp : Lean.PrettyPrinter.Unexpander
| `($_ $f:term $arg:term) =>
   match f, arg with
   | `(term| lambda! $f:ident), `(term| lambda! $arg:lang) =>
      `(lambda! $f:ident ($arg))
   | `(term| lambda! $f:lang), `(term| lambda! $arg:lang) =>
      `(lambda! (($f) ($arg)))
   | _, _ => throw ()
| _ => throw ()

@[app_unexpander Typing.Untyped.Term.lam]
def unexpandTermLam : Lean.PrettyPrinter.Unexpander
| `($_ $x:str $body:term) =>
  match body with
  | `(lambda! $body:lang) =>
    let x := Lean.mkIdent <| Lean.Name.mkStr1 x.getString
    `(lambda! λ $x . $body)
  | _ => throw ()
| _ => throw ()


inductive Statement where | eval (t: Term) | define (name: Ident) (vl: Term)

def Statement.toString : Statement -> String
| .eval t => t.toString
| .define name vl => s!"def {name} := {vl.toString}"
instance : ToString Statement where toString := Statement.toString
