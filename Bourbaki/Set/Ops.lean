import Bourbaki.Set.Basic

universe u v w

namespace Set

variable {α β : Type u} {ι : Sort v}

def image (f : α → β) (s : Set α) : Set β := {f a | a ∈ s}

-- Plus flexible que f <$> univ
def range (f : ι → α) : Set α := {x | ∃ y, f y = x}

-- Surtout pour l'intrudction de `f <$> s`
instance : Functor Set where map := @Set.image

theorem mem_image (f : α → β) (s : Set α) (y : β) : y ∈ f <$> s ↔ ∃ x ∈ s, f x = y := Iff.rfl

def preimage (f : α → β) (s : Set β) : Set α := {x | f x ∈ s}

infixl:80 " ⁻¹ " => preimage

end Set
