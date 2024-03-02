import Std.Tactic.RCases
import Std.Tactic.Ext
import Bourbaki.Set.Ops
import Bourbaki.Logic.Basic

/-
TODO: (noncomputable ?)
  * Surjective => HasSection
  * Injective => HasRetract
  => Simplifier les preuves à partir de sections/rétractions
-/


universe u v w

def Injective (f : α → β) : Prop := ∀ ⦃x y⦄, f x = f y → x = y

/- Composée de deux fonctions injectives est injective -/
theorem Injective.comp {g : β → γ} {f : α → β} (hg : Injective g) (hf : Injective f) :
  Injective (g ∘ f) :=
    fun _ _ =>
      fun h =>
        hf (hg h)

theorem Injective.comp_inj_fst_inj {g : β → γ} {f : α → β} (hc : Injective (g ∘ f)) :
    Injective f := by
  intro x y hfxy
  exact hc (congrArg g hfxy)

def Retract (r : β → α) (f : α → β) : Prop := ∀ x, r (f x) = x

def HasRetract (f : α → β) : Prop := ∃ r, Retract r f

theorem Retract.injective {r : β → α} {f : α → β} : Retract r f → Injective f := by
  intros h x y hfx_eq_fy
  calc
    x = r (f x) := (h x).symm
    _ = r (f y) := (congrArg r hfx_eq_fy)
    _ = y       := h y

theorem HasRetract.injective {f : α → β} : HasRetract f → Injective f :=
  fun h => Exists.elim h (fun _ hr => hr.injective)

theorem Retract.comp {f : α → β} {r : β → α} {f' : β → γ} {r' : γ → β} :
    Retract r f → Retract r' f' → Retract (r ∘ r') (f' ∘ f) := by
  intro hrf hrf' x
  calc
    (r ∘ r') ((f' ∘ f) x) = r (r' (f' (f x))) := rfl
    _                     = r (f x)           := congrArg r (hrf' (f x))
    _                     = x                 := hrf x

theorem Retract.comp' {f : α → β} {r : β → α} {f' : β → γ} {r'' : γ → α} :
    Retract r'' (f' ∘ f) → Retract (r'' ∘ f') f := fun h x => h x


def Surjective (f : α → β) : Prop := ∀ y, ∃ x, f x = y

/- Composée de deux fonctions surjectives est surjective -/
theorem Surjective.comp {g : β → γ} {f : α → β} (hg : Surjective g) (hf : Surjective f) :
  Surjective (g ∘ f) := by
    intro z
    have ⟨y, hy⟩ : ∃ y, g y = z := hg z
    have ⟨x, hx⟩ : ∃ x, f x = y := hf y
    have hz : (g ∘ f) x = z := Eq.trans (congrArg g hx) hy
    exact ⟨x, hz⟩

theorem Surjective.comp_surj_snd_surj {g : β → γ} {f : α → β} (hc : Surjective (g ∘ f)) :
    Surjective g := by
  intro z
  obtain ⟨x, hy⟩ := hc z
  exact ⟨f x, hy⟩

def Section (s : β → α) (f : α → β) : Prop := ∀ x, f (s x) = x
-- Alternativement : Retract s f

def HasSection (f : α → β) : Prop := ∃ s, Section s f

theorem Section.surjective {s : β → α} {f : α → β} (h : Section s f) : Surjective f :=
  fun y => ⟨s y, h y⟩

theorem HasSection.surjective {f : α → β} : HasSection f → Surjective f
  | ⟨_, hs⟩ => hs.surjective

theorem Section.comp {f : α → β} {s : β → α} {f' : β → γ} {s' : γ → β} :
    Section s f → Section s' f' → Section (s ∘ s') (f' ∘ f) := by
  intro hsf hsf' x
  calc
    (f' ∘ f) ((s ∘ s') x) = f' (f (s (s' x))) := rfl
    _                     = f' (s' x)         := congrArg f' (hsf (s' x))
    _                     = x                 := hsf' x


def Bijective (f : α → β) : Prop := Injective f ∧ Surjective f

/- Composée de deux fonctions bijective est bijective -/
theorem Bijective.comp {g : β → γ} {f : α → β} : Bijective g → Bijective f → Bijective (g ∘ f)
  | ⟨hg_inj, hg_surj⟩, ⟨hf_inj, hf_surj⟩ => ⟨hg_inj.comp hf_inj, hg_surj.comp hf_surj⟩


-- TODO: Théorème 1.{e,f}) Livre I § 1 p.71

-- TODO: Prove and find name
example {g : α → β} {f : α → γ} (hg : HasSection g) : (∀ x y : α, (g x = g y) → (f x = f y)) ↔ ∃! h : β → γ, (f = h ∘ g) := by sorry

theorem im_union {f : α → β} {X : Set (Set α)} : f <$> (⋃₀ X) = ⋃₀ ((f <$> ·) <$> X) := by
  ext1 x
  sorry
