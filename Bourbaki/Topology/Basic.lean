import Bourbaki.Set.Functions

/- set_option autoImplicit true -/

universe u v w

open Set

class TopologicalSpace (α : Type u) where
  IsOpen : Set α → Prop
  protected isOpen_univ : IsOpen univ
  protected isOpen_union : ∀ s, (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)
  protected isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)

section Continunous

variable[TopologicalSpace α] [TopologicalSpace β]

open TopologicalSpace

structure Continuous (f : α → β) : Prop where
  isOpen_preimage : ∀ (s : Set β), IsOpen s → IsOpen (f ⁻¹ s)

/- Homéomorphismes d'espaces topologiques -/
structure Homeomorph (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] where
  to : X → Y
  inv : Y → X
  left_inv : Retract inv to
  right_inv : Section to inv
  continuous_to : Continuous to
  continuous_inv : Continuous inv

infixl:25 " ≃ₜ " => Homeomorph

class IsClosed {α : Type u} [TopologicalSpace α] (s : Set α) : Prop where
  isOpen_compl : IsOpen sᶜ

@[simp]
theorem isClosed_iff_compOpen {α : Type u} [TopologicalSpace α] {s : Set α} : IsOpen sᶜ ↔ IsClosed s :=
  ⟨fun h => ⟨h⟩, fun h => h.isOpen_compl⟩

def TopologicalSpace.fromClosed {α : Type u} (T : Set (Set α)) (empty_mem : ∅ ∈ T)
    (inter_mem : ∀ F, F ⊆ T → ⋂₀ F ∈ T)
    (union_mem : ∀ s t, s ∈ T → t ∈ T → s ∪ t ∈ T) : TopologicalSpace α where
  IsOpen X := Xᶜ ∈ T
  isOpen_univ := by simp [empty_mem]
  isOpen_union := by sorry
  isOpen_inter := by
    simp only [Set.compl_sUnion]

end Continunous
