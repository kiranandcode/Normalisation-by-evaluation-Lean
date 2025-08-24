import LeanTyping.Utils
import LeanTyping.Syntax
import LeanTyping.Basic

namespace Typing.Closure

structure Generic (Term V: Type) where
  env: List (String × V)
  var: Ident
  body: Term

abbrev Env V := List (String × V)

partial def Generic.toString [ToString Term] (VtoString : V -> String) : Generic Term V -> String
| ⟨env, var, body⟩ =>
  let env := env.map (fun (k,v) => s!"{k} : ({VtoString v})") |> List.intersperse ", " |> String.join
  s!"{env} ⊢ λ {var} . {body}"

namespace Basic
structure Closure (Term: Type) where
  val: Generic Term (Closure Term)

def Closure.body : Closure Term -> Term := fun clo => clo.val.body
def Closure.var : Closure Term -> Ident := fun clo => clo.val.var
def Closure.env : Closure Term -> Env (Closure Term) := fun clo => clo.val.env

partial def Closure.toString [ToString Term] : Closure Term -> String :=
   fun clo => clo.val.toString Closure.toString
instance [ToString Term] : ToString (Closure Term) where toString := Closure.toString

def Closure.make (env: Env (Closure Term)) (var: Ident) (body: Term) : Closure Term :=
   Closure.mk (Generic.mk env var body)

end Basic

mutual
  partial def unexpandClosureBinding : Lean.TSyntax `term -> Lean.PrettyPrinter.UnexpandM (Lean.TSyntax `closureBinding)
     | `(term| ($t1:term, $t2:term)) =>
        match t1, t2 with
        | `(term| $s:ident), `(term| $vl:term) => do
          let vl <- unexpandClosureInner vl
          `(closureBinding| $s:ident : ( $vl ))
        | `(term| $s:str), `(term| $vl:term) => do
          let s := Lean.mkIdent <| Lean.Name.mkStr1 s.getString
          let vl <- unexpandClosureInner vl
          `(closureBinding| $s:ident : ( $vl ))
        | _, _ => `(closureBinding| (($t1:term , $t2:term)))
     | `(term| $t:ident) => `(closureBinding| $t:ident)
     | `(term| $t1:term) => `(closureBinding| ($t1))

  partial def unexpandClosureInner : Lean.TSyntax `term -> Lean.PrettyPrinter.UnexpandM (Lean.TSyntax `closure)
     | `($_ [$cb,*] $v:str $body:term) => 
        match body with
        | `(lambda! $body:lang) => do
          let cb <- cb.getElems.toList.mapM unexpandClosureBinding
          let cb := cb.toArray
          let v := Lean.mkIdent <| Lean.Name.mkStr1 v.getString
          `(closure| $cb:closureBinding,* ⊢ λ $v . $body)
        | _ => throw ()
     | _ => throw ()
end

@[app_unexpander Basic.Closure.mk]
def unexpandClosure : Lean.PrettyPrinter.Unexpander
| `(term| $t:term) => unexpandClosureInner t


