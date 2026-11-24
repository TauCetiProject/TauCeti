/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Sum.Basic
public import Mathlib.Basic.IsEmpty.Defs
public import Mathlib.Basic.Nontrivial.Defs

/-!
# Sum types: distinct pairs and injective maps out of a sum

In `α ⊕ α`, each label `p` has a partner `p.swap` with the same underlying element of `α`. Two
labels that are neither equal nor partners have distinct underlying elements, so `α` has at least
two elements.

A map `Sum.elim f g` out of a sum stays injective when its two parts are reindexed by injective
maps, and it is injective as soon as `f` is when the second summand is empty. A map
`Sum.elim (Sum.elim f g) h` out of a nested sum stays injective when its two inner parts are
exchanged and all three parts are reindexed by injective maps.

## Main results

* `Sum.nontrivial_of_ne_of_ne_swap`: if `q ≠ p` and `q ≠ p.swap` in `α ⊕ α`, then `α` is
  nontrivial.
* `Function.Injective.sumElim_comp`: if `Sum.elim f g` is injective, so is
  `Sum.elim (f ∘ e₁) (g ∘ e₂)` for injective `e₁`, `e₂`.
* `Function.Injective.sumElim_of_isEmpty`: if `f` is injective and `β` is empty, then
  `Sum.elim f g` is injective for every `g : β → γ`.
* `Function.Injective.sumElim_sumElim_swap_comp`: if `Sum.elim (Sum.elim f g) h` is injective, so
  is `Sum.elim (Sum.elim (g ∘ e₂) (f ∘ e₁)) (h ∘ e₃)` for injective `e₁`, `e₂`, `e₃`.
-/

public section

namespace Sum

variable {α : Type*}

/-- If two labels of `α ⊕ α` are neither equal nor partners under `Sum.swap`, then their underlying
elements of `α` differ, so `α` is nontrivial. -/
theorem nontrivial_of_ne_of_ne_swap {p q : α ⊕ α} (h : q ≠ p) (h' : q ≠ p.swap) :
    Nontrivial α := by
  rcases p with a | a <;> rcases q with b | b <;>
    exact ⟨b, a, fun hba => by subst hba; simp_all⟩

end Sum

namespace Function.Injective

variable {α α' β β' : Type*} {γ : Sort*} {f : α → γ} {g : β → γ}

/-- Reindexing the two parts of an injective map out of a sum by injective maps gives an injective
map. -/
theorem sumElim_comp (h : Injective (Sum.elim f g)) {e₁ : α' → α} {e₂ : β' → β}
    (he₁ : Injective e₁) (he₂ : Injective e₂) : Injective (Sum.elim (f ∘ e₁) (g ∘ e₂)) := by
  rw [← Sum.elim_comp_map]
  exact h.comp (he₁.sumMap he₂)

/-- A map out of a sum whose second summand is empty is injective as soon as its first part is. -/
theorem sumElim_of_isEmpty [IsEmpty β] (hf : Injective f) (g : β → γ) :
    Injective (Sum.elim f g) :=
  hf.sumElim (injective_of_subsingleton g) fun _ b => isEmptyElim b

/-- Exchanging the two inner parts of an injective map out of a nested sum, and reindexing the
three parts by injective maps, gives an injective map. -/
theorem sumElim_sumElim_swap_comp {δ δ' : Type*} {h : δ → γ}
    (H : Injective (Sum.elim (Sum.elim f g) h)) {e₁ : α' → α} {e₂ : β' → β} {e₃ : δ' → δ}
    (he₁ : Injective e₁) (he₂ : Injective e₂) (he₃ : Injective e₃) :
    Injective (Sum.elim (Sum.elim (g ∘ e₂) (f ∘ e₁)) (h ∘ e₃)) := by
  have hcomp : Sum.elim (Sum.elim (g ∘ e₂) (f ∘ e₁)) (h ∘ e₃) =
      Sum.elim (Sum.elim f g) h ∘ Sum.map (Sum.swap ∘ Sum.map e₂ e₁) e₃ := by
    ext ((_ | _) | _) <;> rfl
  rw [hcomp]
  exact H.comp ((Sum.swap_leftInverse.injective.comp (he₂.sumMap he₁)).sumMap he₃)

end Function.Injective
