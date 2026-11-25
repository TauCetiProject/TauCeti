/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Monoid.Prod
public import TauCeti.Algebra.Order.Group.DimensionGroup.Scale

/-!
# Checks for scales of ordered abelian groups

Examples and non-examples of scales (`TauCeti.IsScale`) in `ℤ` and in `ℤ²` with the product
order.

* In `ℤ`, `[0, 2] = {0, 1, 2}` is a scale (the scale of `M₂`), `{0, 1, 3}` is not, being not
  hereditary (`0 ≤ 2 ≤ 3` with `2` missing), the positive cone `ℕ` is a scale (the scale of the
  compact operators), and `{0}` is not a scale, since the positive cone of `ℤ` is nonzero.
* In `ℤ²` with the product order, `[0, (1, 1)]` is a scale (the scale of `ℂ ⊕ ℂ`), while
  `[0, (1, 0)] ∪ [0, (0, 1)]` is not, being not upward directed: an upper bound of `(1, 0)` and
  `(0, 1)` is at least `(1, 1)`.
-/

public section

namespace TauCeti.ScaleExamples

/-- **Check.** In `ℤ`, the interval `[0, 2]` is a scale: `2` is an order unit. -/
theorem isScale_Icc_zero_two : IsScale (Set.Icc (0 : ℤ) 2) := by
  refine (isScale_Icc_iff HasRieszInterpolation.of_semilatticeSup).2
    ⟨by decide, fun g hg ↦ ⟨g.toNat, ?_⟩⟩
  rw [Int.nsmul_eq_mul]
  omega

/-- The interval `[0, 2]` of `ℤ` is `{0, 1, 2}`. -/
theorem Icc_zero_two : Set.Icc (0 : ℤ) 2 = {0, 1, 2} := by
  ext g
  simp only [Set.mem_Icc, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- **Check.** In `ℤ`, `{0, 1, 3}` is not a scale: it is not hereditary, since `0 ≤ 2 ≤ 3` and
`2` is missing. -/
theorem not_isScale_zero_one_three : ¬ IsScale ({0, 1, 3} : Set ℤ) := fun h ↦ by
  have h2 := h.mem_of_nonneg_of_le (g := 2) (s := 3) (by decide) (by decide) (by simp)
  simp at h2

/-- **Check.** In `ℤ`, the positive cone `ℕ` is a scale. -/
theorem isScale_Ici_zero : IsScale (Set.Ici (0 : ℤ)) :=
  isScale_Ici

/-- **Check.** In `ℤ`, `{0}` is not a scale: the positive cone contains `1 ≠ 0`. -/
theorem not_isScale_singleton_zero : ¬ IsScale ({0} : Set ℤ) := fun h ↦
  one_ne_zero (isScale_singleton_zero_iff.1 h zero_le_one)

/-- **Check.** In `ℤ²` with the product order, the interval `[0, (1, 1)]` is a scale: `(1, 1)` is
an order unit. -/
theorem isScale_Icc_zero_one_one : IsScale (Set.Icc (0 : ℤ × ℤ) (1, 1)) := by
  refine (isScale_Icc_iff HasRieszInterpolation.of_semilatticeSup).2
    ⟨by simp [Prod.le_def], fun g hg ↦ ⟨g.1.toNat + g.2.toNat, ?_⟩⟩
  rw [Prod.le_def] at hg ⊢
  simp only [Prod.smul_mk, Prod.fst_zero, Prod.snd_zero, Int.nsmul_eq_mul, mul_one] at hg ⊢
  omega

/-- **Check.** In `ℤ²` with the product order, `[0, (1, 0)] ∪ [0, (0, 1)]` is not a scale: it is
not upward directed, since an upper bound of `(1, 0)` and `(0, 1)` is at least `(1, 1)`. -/
theorem not_isScale_union :
    ¬ IsScale (Set.Icc (0 : ℤ × ℤ) (1, 0) ∪ Set.Icc (0 : ℤ × ℤ) (0, 1)) := fun h ↦ by
  obtain ⟨z, hz, h₁, h₂⟩ := h.directedOn (1, 0) (Or.inl (by simp [Prod.le_def]))
    (0, 1) (Or.inr (by simp [Prod.le_def]))
  simp only [Set.mem_union, Set.mem_Icc, Prod.le_def, Prod.fst_zero, Prod.snd_zero] at hz h₁ h₂
  omega

end TauCeti.ScaleExamples
