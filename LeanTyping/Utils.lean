import Lean

def List.assoc [BEq A] : List (A × B) -> A -> Option B :=
  fun ls vl => ls.findSome? (fun (k,v) => if k == vl then .some v else .none)

structure Ident where
  base: String
  count: Nat
deriving Hashable, DecidableEq

instance : BEq Ident where
  beq := fun ⟨b1, c1⟩ ⟨b2, c2⟩ => b1 == b2 && c1 == c2

instance : LawfulBEq Ident where
  rfl := by simp [BEq.beq]
  eq_of_beq := by intros p1 p2; rcases p1 with (⟨p1b,p1c⟩); rcases p2 with (⟨p2b,p2c⟩); simp [BEq.beq]


def Ident.next : Ident -> Ident
| id => ⟨id.base, id.count + 1⟩

instance : ToString Ident where
  toString := fun ⟨base, cnt⟩ => if cnt == 0 then base else s!"{base}{cnt}"

instance : Coe String Ident where
  coe := fun s => Ident.mk s 0
instance : Coe Ident String where
  coe := fun s => s!"{s}"


