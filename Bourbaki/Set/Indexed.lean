import Bourbaki.Set.Basic
import Bourbaki.Set.Functions
import Bourbaki.Set.Ops

universe u v w

namespace Set

variable {α : Type u} {β : Type v} {ι : Sort w}

-- Définition 1 p. 74
-- En réalité {x | ∃ i, i ∈ ι ∧ i ∈ Xᵢ}
-- où Xᵢ:= s i
def iUnion (s : ι → Set α) : Set α := Set.sUnion (range s)

open Std.ExtendedBinder in
syntax "⋃ (" extBinder "), " term:60 : term

macro_rules
  | `(⋃ ($x:ident : $t), $p) => `(iUnion (fun $x:ident : $t => $p))


-- Définition 2
-- En réalité {x | ∀ i, i ∈ ι → x ∈ Xᵢ}
def iInter (s : ι → Set α) : Set α := Set.sInter (range s)

open Std.ExtendedBinder in
syntax "⋂ (" extBinder "), " term:60 : term

macro_rules
  | `(⋂ ($x:ident : $t), $p) => `(iInter (fun $x:ident : $t => $p))


@[simp]
theorem mem_iUnion {x : α} {s : ι → Set α} : x ∈ ⋃ (i : ι), s i ↔ ∃ i, x ∈ s i :=
  by
    apply Iff.intro
    . intro ⟨_, ⟨⟨a, (t_eq : s a = _)⟩, h⟩⟩
      exact ⟨a, t_eq.symm ▸ h⟩
    . intro ⟨a, h⟩
      exact ⟨s a, ⟨⟨a, rfl⟩, h⟩⟩

@[simp]
theorem mem_iInter {x : α} {s : ι → Set α} : x ∈ ⋂ (i : ι), s i ↔ ∀ i, x ∈ s i :=
  by
    apply Iff.intro
    . intro h a
      exact h (s a) ⟨a, rfl⟩
    . intro h _ ⟨a, eq⟩
      exact eq ▸ h a

theorem image_iUnion {f : α → β} {s : ι → Set α} : f '' ⋃ (i : ι), s i = ⋃ (i : ι), f '' s i :=
  by
    ext1 x
    simp only [mem_image, mem_iUnion, ←exists_and_right, ←exists_and_left]
    rw [exists_swap]

theorem image_iInter_subset {f : α → β} {s : ι → Set α} : f '' ⋂ (i : ι), s i ⊆ ⋂ (i : ι), f '' s i :=
  by
    intro y ⟨x, ⟨hx, hxy⟩⟩
    simp only [mem_iInter] at *
    exact fun i => ⟨x, ⟨hx i, hxy⟩⟩

theorem preimage_iInter {f : α → β} {s : ι → Set β} : f ⁻¹' ⋂ (i : ι), s i = ⋂ (i : ι), f ⁻¹' (s i) :=
  by ext1; simp [mem_preimage]

end Set
