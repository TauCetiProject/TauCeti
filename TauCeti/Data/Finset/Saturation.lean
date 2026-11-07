/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Card
public import Lean.Elab.Tactic.Omega

/-!
# Bounded saturation of a finite set

An inflationary finite-set step reaches a fixed point after at most the
cardinality of the universe many strict additions. The implementation stops
as soon as it reaches a fixed point. No enumeration of subsets is used.
-/

@[expose] public section

namespace TauCeti.FiniteClosure

variable {α : Type*} [DecidableEq α]

/-- Apply a finite-set step at most `fuel` times, stopping at a fixed point. -/
def saturate (step : Finset α → Finset α) : ℕ → Finset α → Finset α
  | 0, s => s
  | fuel + 1, s =>
      let t := step s
      if t = s then s else saturate step fuel t

theorem subset_saturate (step : Finset α → Finset α)
    (hinflate : ∀ s, s ⊆ step s) (fuel : ℕ) (s : Finset α) :
    s ⊆ saturate step fuel s := by
  induction fuel generalizing s with
  | zero => exact Finset.Subset.refl _
  | succ fuel ih =>
    simp only [saturate]
    split
    · exact Finset.Subset.refl _
    · exact (hinflate s).trans (ih (step s))

theorem saturate_subset (step : Finset α → Finset α) (fuel : ℕ)
    {s t : Finset α} (hst : s ⊆ t)
    (hclosed : ∀ u, u ⊆ t → step u ⊆ t) :
    saturate step fuel s ⊆ t := by
  induction fuel generalizing s with
  | zero => exact hst
  | succ fuel ih =>
    simp only [saturate]
    split
    · exact hst
    · exact ih (hclosed s hst)

theorem saturate_preserves (step : Finset α → Finset α) (fuel : ℕ)
    (property : Finset α → Prop) (hstep : ∀ s, property s → property (step s))
    {s : Finset α} (hs : property s) :
    property (saturate step fuel s) := by
  induction fuel generalizing s with
  | zero => exact hs
  | succ fuel ih =>
    simp only [saturate]
    split
    · exact hs
    · exact ih (hstep s hs)

/-- The size deficit decreases whenever an inflationary step changes the set. -/
theorem saturate_fixed [Fintype α] (step : Finset α → Finset α)
    (hinflate : ∀ s, s ⊆ step s) (fuel : ℕ) (s : Finset α)
    (hbudget : Fintype.card α ≤ s.card + fuel) :
    step (saturate step fuel s) = saturate step fuel s := by
  induction fuel generalizing s with
  | zero =>
    have hs : s = Finset.univ :=
      Finset.eq_of_subset_of_card_le (Finset.subset_univ s) (by simpa using hbudget)
    simp only [saturate]
    have hreverse : step s ⊆ s := by
      rw [hs]
      exact Finset.subset_univ _
    exact hreverse.antisymm (hinflate s)
  | succ fuel ih =>
    simp only [saturate]
    split
    · assumption
    · have hstrict : s.card < (step s).card :=
        Finset.card_lt_card ⟨hinflate s, by
          intro hreverse
          exact ‹step s ≠ s› (hreverse.antisymm (hinflate s))⟩
      exact ih (step s) (by omega)

/-- Saturation with the universe cardinality always terminates at a fixed point. -/
theorem saturate_card_fixed [Fintype α] (step : Finset α → Finset α)
    (hinflate : ∀ s, s ⊆ step s) (s : Finset α) :
    step (saturate step (Fintype.card α) s) =
      saturate step (Fintype.card α) s :=
  saturate_fixed step hinflate _ s (by omega)


end TauCeti.FiniteClosure
