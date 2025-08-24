import Lean

declare_syntax_cat ty
syntax "ℕ" : ty
syntax ident: ty
syntax ty:30 " → " ty:10 : ty
syntax "(" ty ")" : ty
syntax "type!" ty : term

private def Typing.Syntax.Ty.arrow := Lean.mkIdent (.mkStr2 "Ty" "arrow")
private def Typing.Syntax.Ty.nat := Lean.mkIdent (.mkStr2 "Ty" "nat")

partial def Typing.Syntax.expandType : Lean.TSyntax `ty -> Lean.MacroM (Lean.TSyntax `term)
| `(ty| $id:ident) => `(term| $id:ident)
| `(ty| ($t:ty)) => expandType t
| `(ty| ℕ) => `(term| $Typing.Syntax.Ty.nat)
| `(ty| $t1:ty → $t2:ty) => do
  let t1 <- expandType t1
  let t2 <- expandType t2
  `(term| $Typing.Syntax.Ty.arrow $t1 $t2)
| _ => Lean.Macro.throwUnsupported

macro_rules
| `(term| type! $t:ty) => Typing.Syntax.expandType t

declare_syntax_cat lang
syntax parenthesizedLang := ident <|> ("(" lang ")")
syntax ident : lang
syntax "λ" ident " . " lang : lang
syntax "(" lang ")" : lang
syntax lang withPosition(ppSpace parenthesizedLang) : lang
syntax num : lang
syntax lang " + " num : lang
syntax "rec" "[" (ty <|> ident) "]" parenthesizedLang parenthesizedLang parenthesizedLang : lang
syntax lang " : " (ty <|> ident) : lang
syntax "lambda! " lang : term

namespace Typing.Syntax
private def Term.var := Lean.mkIdent (.mkStr2 "Term" "var")
private def Term.lam := Lean.mkIdent (.mkStr2 "Term" "lam")
private def Term.app := Lean.mkIdent (.mkStr2 "Term" "app")
private def Term.zero := Lean.mkIdent (.mkStr2 "Term" "zero")
private def Term.add1 := Lean.mkIdent (.mkStr2 "Term" "add1")
private def Term.rec_ := Lean.mkIdent (.mkStr2 "Term" "rec_")
private def Term.the := Lean.mkIdent (.mkStr2 "Term" "the")


mutual
partial def expandParenthesisedLambda: Lean.TSyntax `parenthesizedLang -> Lean.MacroM (Lean.TSyntax `term)
| `(parenthesizedLang| $id:ident)  => do
   expandLambda (<- `(lang| $id:ident))
| `(parenthesizedLang| ($l:lang)) => expandLambda l
| _ => Lean.Macro.throwUnsupported


partial def expandLambda : Lean.TSyntax `lang -> Lean.MacroM (Lean.TSyntax `term)
| `(lang| $i:ident) =>
  let str := Lean.Syntax.mkStrLit i.getId.toString
  `(term| $Term.var $str)
| `(lang| λ $x:ident . $body:lang) => do
  let body <- expandLambda body
  let x := Lean.Syntax.mkStrLit x.getId.toString
  `(term| $Term.lam $x $body)
| `(lang| $f:lang $arg:parenthesizedLang) => do
  let f <- expandLambda f
  let arg <- expandParenthesisedLambda arg
  `(term| $Term.app $f $arg)
| `(lang| $n:num) => do
   let mut n := n.getNat
   let mut res <- `(term| $Term.zero)
   while n > 0 do
     res <- `(term| $Term.add1 $res)
     n := n - 1
   pure res
| `(lang| $l:lang + $n:num) => do
   let mut n := n.getNat
   let mut res <- expandLambda l
   while n > 0 do
     res <- `(term| $Term.add1 $res)
     n := n - 1
   pure res
| `(lang|
  rec [$ty:ty] $n:parenthesizedLang $b:parenthesizedLang $s:parenthesizedLang ) => do
    let n <- expandParenthesisedLambda n
    let b <- expandParenthesisedLambda b
    let s <- expandParenthesisedLambda s
    let ty <- Typing.Syntax.expandType ty
    `(term| $Term.rec_ $ty $n $b $s)
| `(lang| $l:lang : $ty:ty) => do
   let l <- expandLambda l
   let ty <- expandType ty
   `(term| $Term.the $l $ty)

| `(lang| ($l:lang)) => expandLambda l
| _ => Lean.Macro.throwUnsupported

end

end Typing.Syntax

macro_rules
| `(term| lambda! $l:lang) => Typing.Syntax.expandLambda l

declare_syntax_cat closureBinding
declare_syntax_cat closure
syntax ident " : " "(" closure " )" : closureBinding
syntax ident : closureBinding
syntax "(" term  " )" : closureBinding
syntax closureBinding,* " ⊢ " "λ " ident " . " lang ppSpace : closure
syntax "closure!" closure : term

namespace Typing.Syntax

def expandClosureBinding : Lean.TSyntax `closureBinding -> Lean.MacroM (Lean.TSyntax `term)
| `(closureBinding| $s:ident : ( $vl:closure ) ) => do
  let s := Lean.Syntax.mkStrLit s.getId.toString
  `(term| [($s, closure! $vl)])
| `(closureBinding| $s:ident ) => `(term| $s)
| `(closureBinding| ($t:term) ) => `(term| [$t])
| _ => Lean.Macro.throwUnsupported

partial def expandClosureBindings : List (Lean.TSyntax `closureBinding) -> Lean.MacroM (Lean.TSyntax `term) :=
  fun ls => do
    let ls <- ls.mapM expandClosureBinding
    let ls := ls.toArray
    `(term| List.flatten [$ls,*])


end Typing.Syntax

private def Typing.Syntax.Closure.make := Lean.mkIdent (.mkStr2 "Closure" "make")

macro_rules
| `(term| closure! $cbs:closureBinding,* ⊢ λ $v:ident . $body:lang) => do
   let cbs <- Typing.Syntax.expandClosureBindings cbs.getElems.toList
   let v := Lean.Syntax.mkStrLit v.getId.toString
   let body <- Typing.Syntax.expandLambda body
   `(term| $Typing.Syntax.Closure.make $cbs $v $body)


declare_syntax_cat statement
syntax lang : statement
syntax "def " ident " := " "(" withPosition(lang) ")" : statement
syntax "program:" withPosition(lineEq (ppLine colGe statement)*) : term

namespace Typing.Syntax

private def Statement.define  :=  Lean.mkIdent (.mkStr2 "Statement" "define")
private def Statement.eval  :=  Lean.mkIdent (.mkStr2 "Statement" "eval")

def elabStatement : Lean.TSyntax `statement -> Lean.MacroM (Lean.TSyntax `term)
| `(statement| def $id:ident := ($vl)) => do
  let id := Lean.Syntax.mkStrLit id.getId.toString
  let vl <- expandLambda vl
  `(term| $Statement.define $id $vl)
| `(statement| $vl:lang) => do
  let vl <- expandLambda vl
  `(term| $Statement.eval $vl)
| _ => Lean.Macro.throwUnsupported

end Typing.Syntax

macro_rules
| `(program:
    $[
     $st:statement
     ]*) => do
  let stmts <- st.toList.mapM Typing.Syntax.elabStatement
  let stmts := stmts.toArray
  `(term| [$stmts,*])

