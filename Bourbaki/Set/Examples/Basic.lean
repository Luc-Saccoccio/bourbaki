import Bourbaki.Set.Basic

universe u v w

-- Proposition 1
example : ∀ x : Set α, x ⊆ x :=
  by
    intros _ _ hz
    exact hz

example : ∀ x y z : Set α, (x ⊆ y ∧ y ⊆ z) → x ⊆ z :=
  by
    intros _ y _ hxyz _ h
    exact hxyz.right (hxyz.left h)
