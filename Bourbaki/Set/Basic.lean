import Lean.Parser.Term
import Std.Classes.SetNotation
import Std.Tactic.Ext
import Bourbaki.Logic.Basic

universe u v w

def Set (α : Type u) : Type u := α → Prop

def setFrom {α : Type u} (p : α → Prop) : Set α := p

namespace Set

variable {α : Type u}

protected def Mem (a : α) (s : Set α) : Prop := s a

instance : Membership α (Set α) := ⟨Set.Mem⟩

/--
"Axiome d'extensionnalité" prouvé avec l'extensionnalité fonctionnelle et
l'extensionnalité propositionnelle
-/
@[ext]
theorem setext {a b : Set α} (h : ∀ (x : α), x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x => propext (h x))

protected def Subset (s₁ s₂ : Set α) := ∀ ⦃a⦄, a ∈ s₁ → a ∈ s₂

/-- Lean4 possède déjà des classes pour les notations `⊆` et `∅` --/
instance : HasSubset (Set α) := ⟨Set.Subset⟩

theorem msub_iff_eq {a b : Set α} : (a ⊆ b ∧ b ⊆ a) ↔ a = b := by
  apply Iff.intro
  . intro ⟨hab, hba⟩
    have h₁ : ∀ x : α , x ∈ a → x ∈ b := fun _ hx => hab hx
    have h₂ : ∀ x : α , x ∈ b → x ∈ a := fun _ hx => hba hx
    exact setext (fun x => ⟨h₁ x, h₂ x⟩)
  . intro h
    have h₁ : a ⊆ b := fun x hx => by rw [h] at hx; exact hx
    have h₂ : b ⊆ a := fun x hx => by rw [h.symm] at hx; exact hx
    exact ⟨h₁, h₂⟩

instance : EmptyCollection (Set α) := ⟨λ _ => False⟩

theorem empty_sub {a : Set α} : ∅ ⊆ a := fun _ hx => False.elim hx

theorem subempty_eq_empty {a : Set α} : a ⊆ ∅ → a = ∅ :=
  fun h => Iff.mp msub_iff_eq (And.intro h empty_sub)

/-
"Schéma d'axiomes de compréhension"
Introduction des notations :
  * `{ x | p x}` : Schéma d'axiomes de compréhension
  * `{ p x | q x}` : Équivalent à `{x | p x ∧ q x}
-/
open Std.ExtendedBinder in
syntax "{" extBinder " | " term "}" : term

macro_rules
  | `({ $x:ident | $p }) => `(setFrom (fun $x:ident => $p)) -- Premier cas
  | `({ $x:ident : $t | $p }) => `(setFrom (fun $x:ident : $t => $p)) -- Premier cas avec annotation de type
  | `({ $x:ident $b:binderPred | $p }) => `(setFrom (fun $x:ident => satisfies_binder_pred% $x $b ∧ $p))

/-
  * `{f x | (x : X)}` où `f` est une "fonction" : Équivalente à `{y | ∃ x : X, y = f x}`
-/
open Std.ExtendedBinder in
macro (priority := low) "{" t:term " | " bs:extBinders "}" : term =>
  `({x | ∃ᵉ $bs:extBinders, $t = x})

def univ : Set α := {_x | True}

protected def insert (a : α) (s : Set α) : Set α := {b | b = a ∨ b ∈ s}

instance : Insert α (Set α) := ⟨Set.insert⟩

protected def singleton (a : α) : Set α := {b | b = a}

instance : Singleton α (Set α) := ⟨Set.singleton⟩

protected def union (s₁ s₂ : Set α) : Set α := {x | s₁ x ∨ s₂ x}

instance : Union (Set α) := ⟨Set.union⟩

def sUnion (S : Set (Set α)) : Set α := {x | ∃ t ∈ S, x ∈ t}

prefix:110 "⋃₀ " => sUnion

protected def inter (s₁ s₂ : Set α) : Set α := {x | s₁ x ∧ s₂ x}

instance : Inter (Set α) := ⟨Set.inter⟩

def sInter (S : Set (Set α)) : Set α := {x | ∀ t ∈ S, x ∈ t}

prefix:110 "⋂₀ " => sInter

def compl (s : Set α) : Set α := {x | x ∉ s}

postfix:1024 "ᶜ" => compl

theorem compl_compl_eq_id {a : Set α} : (aᶜ)ᶜ = a := by
  calc
    (aᶜ)ᶜ = {x | ¬¬a x} := by rfl
    _     = a           := by simp [propext dne]; rfl

@[simp]
theorem univCompl_eq_empty {α : Type u} : (@univ α)ᶜ = ∅ := by
  have hsub : (@univ α)ᶜ ⊆ ∅ := by
    intro x hx
    have hx'' : ¬True := hx
    have hx''' : False := by simp at hx''
    exact False.elim hx'''
  exact subempty_eq_empty hsub

protected def diff (s₁ s₂ : Set α) : Set α := {x ∈ s₁ | x ∉ s₂}

instance : SDiff (Set α) := ⟨Set.diff⟩

def powerset (s : Set α) : Set (Set α) := {t | t ⊆ s}

prefix:100 "𝒫 " => powerset

end Set
