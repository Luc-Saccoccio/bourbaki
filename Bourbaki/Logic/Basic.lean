open Classical

private theorem _dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

theorem dne {p : Prop} : ¬¬p ↔ p := by
  apply Iff.intro
  . exact _dne
  . intro h
    exact Or.elim (em (¬¬p))
      (fun hp : ¬¬p => hp)
      (fun hnp : ¬¬¬p => absurd h (_dne hnp))

def ExistsUnique (p : α → Prop) : Prop := ∃ x, (p x ∧ ∀ y, p y → y = x)

open Lean TSyntax.Compat in
macro "∃!" xs:explicitBinders ", " b:term : term => expandExplicitBinders ``ExistsUnique xs b

theorem exists_swap {p : α → β → Prop} : (∃ x y, p x y) ↔ (∃ y x, p x y) :=
  ⟨fun ⟨x, y, h⟩ => ⟨y, x, h⟩, fun ⟨y, x, h⟩ => ⟨x, y, h⟩⟩
