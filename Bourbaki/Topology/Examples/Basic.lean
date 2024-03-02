import Bourbaki.Topology.Basic
import Bourbaki.Set.Basic

universe u v w

variable (X : Type u)

open Set

instance discreteSpace : TopologicalSpace X where
  IsOpen := fun _ => true
  isOpen_univ := rfl
  isOpen_union := fun _ _ => by rfl
  isOpen_inter := fun _ _ _ _ => by rfl

instance trivialTop : TopologicalSpace X where
  IsOpen := fun x => x = univ ∨ x = ∅
  isOpen_univ := Or.inl rfl
  isOpen_union := sorry
  isOpen_inter := sorry

