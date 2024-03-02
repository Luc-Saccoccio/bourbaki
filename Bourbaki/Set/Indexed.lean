import Bourbaki.Set.Basic
import Bourbaki.Set.Functions
import Bourbaki.Set.Ops

universe u v w

namespace Set

variable {α : Type u} {ι : Sort v}

-- Définition 1 p. 74
-- En réalité {x | ∃ i, i ∈ ι ∧ i ∈ Xᵢ}
-- où Xᵢ:= s i
def iUnion (s : ι → Set α) : Set α := Set.sUnion (range s)

-- Définition 2
-- En réalité {x | ∀ i, i ∈ ι → x ∈ Xᵢ}
def iInter (s : ι → Set α) : Set α := Set.sInter (range s)

end Set
