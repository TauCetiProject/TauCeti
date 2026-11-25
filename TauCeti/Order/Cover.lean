/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Order.Cover

/-!
# Transpositions of covering pairs in a linear order

In a linear order, if `a ⋖ b`, no element lies strictly between `a` and `b`, so `a` and `b` bear
the same strict order relation to every element outside `{a, b}`. Consequently `Equiv.swap a b`
preserves `<` on every pair of inputs except `(a, b)` and `(b, a)`, which it reverses.

## Main results

* `CovBy.lt_iff_lt_of_ne_left` and `CovBy.lt_iff_lt_of_ne_right`: for `a ⋖ b`, `a` and `b` bear
  the same strict order relation to every element outside `{a, b}`.
* `CovBy.swap_lt_swap_iff_of_ne`: for `a ⋖ b`, `Equiv.swap a b` preserves strict inequality on
  every pair other than `(a, b)` and `(b, a)`.
* `CovBy.swap_lt_swap_iff`: full characterization of `Equiv.swap a b c < Equiv.swap a b d` when
  `a ⋖ b`.
-/

public section

namespace CovBy

variable {α : Type*} [LinearOrder α] {a b c d : α}

/-- If `a ⋖ b` in a linear order, any element `c ≠ a` satisfies `c < b ↔ c < a`. -/
theorem lt_iff_lt_of_ne_left (h : a ⋖ b) (hc : c ≠ a) : c < b ↔ c < a := by
  rw [h.lt_iff_le_left, le_iff_lt_or_eq, or_iff_left hc]

/-- If `a ⋖ b` in a linear order, any element `c ≠ b` satisfies `a < c ↔ b < c`. -/
theorem lt_iff_lt_of_ne_right (h : a ⋖ b) (hc : c ≠ b) : a < c ↔ b < c := by
  rw [h.lt_iff_le_right, le_iff_lt_or_eq, or_iff_left hc.symm]

variable [DecidableEq α]

/-- If `a ⋖ b` in a linear order, `a` and `b` have identical strict order relations with every
other element, so `Equiv.swap a b` preserves `<` on every pair other than `(a, b)` and
`(b, a)`. -/
theorem swap_lt_swap_iff_of_ne (h : a ⋖ b) (h₁ : ¬(c = a ∧ d = b)) (h₂ : ¬(c = b ∧ d = a)) :
    Equiv.swap a b c < Equiv.swap a b d ↔ c < d := by
  by_cases hca : c = a
  · by_cases hdb : d = b
    · exact (h₁ ⟨hca, hdb⟩).elim
    by_cases hda : d = a
    · simp [hca, hda]
    · rw [hca, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hda hdb]
      exact (h.lt_iff_lt_of_ne_right hdb).symm
  by_cases hcb : c = b
  · by_cases hda : d = a
    · exact (h₂ ⟨hcb, hda⟩).elim
    by_cases hdb : d = b
    · simp [hcb, hdb]
    · rw [hcb, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hda hdb]
      exact h.lt_iff_lt_of_ne_right hdb
  by_cases hda : d = a
  · rw [hda, Equiv.swap_apply_of_ne_of_ne hca hcb, Equiv.swap_apply_left]
    exact h.lt_iff_lt_of_ne_left hca
  by_cases hdb : d = b
  · rw [hdb, Equiv.swap_apply_of_ne_of_ne hca hcb, Equiv.swap_apply_right]
    exact (h.lt_iff_lt_of_ne_left hca).symm
  rw [Equiv.swap_apply_of_ne_of_ne hca hcb, Equiv.swap_apply_of_ne_of_ne hda hdb]

/-- Full characterization of `Equiv.swap a b c < Equiv.swap a b d` for a covering pair `a ⋖ b` in
a linear order: `(b, a)` becomes ordered, `(a, b)` becomes unordered, and all other pairs keep
their relative order. -/
theorem swap_lt_swap_iff (h : a ⋖ b) :
    Equiv.swap a b c < Equiv.swap a b d ↔ c = b ∧ d = a ∨ ¬(c = a ∧ d = b) ∧ c < d := by
  by_cases h₁ : c = a ∧ d = b
  · rcases h₁ with ⟨rfl, rfl⟩
    simp [h.lt.ne', not_lt_of_gt h.lt]
  by_cases h₂ : c = b ∧ d = a
  · rcases h₂ with ⟨rfl, rfl⟩
    simp [h.lt]
  rw [h.swap_lt_swap_iff_of_ne h₁ h₂]
  simp [h₁, h₂]

end CovBy
