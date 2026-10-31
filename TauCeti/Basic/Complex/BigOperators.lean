/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Complex.Basic

/-!
# Weighted sums of squared absolute values

A finitely supported family of complex numbers `f` and nonnegative real weights `w` give the
real sum `∑ₛ |f s|² w s`. This file records that this sum vanishes exactly when `f` vanishes at
every index of nonzero weight (`Finsupp.sum_normSq_mul_eq_zero_iff`).
-/

public section

namespace Finsupp

/-- A real sum `∑ₛ |f s|² w s` with nonnegative weights vanishes exactly when `f` vanishes at every
index of nonzero weight. -/
theorem sum_normSq_mul_eq_zero_iff {α : Type*} (f : α →₀ ℂ) {w : α → ℝ} (hw : ∀ s, 0 ≤ w s) :
    (f.sum fun s z ↦ Complex.normSq z * w s) = 0 ↔ ∀ s, w s ≠ 0 → f s = 0 := by
  rw [Finsupp.sum, Finset.sum_eq_zero_iff_of_nonneg fun s _ ↦
    mul_nonneg (Complex.normSq_nonneg _) (hw s)]
  refine ⟨fun h s hs ↦ ?_, fun h s _ ↦ ?_⟩
  · by_contra hf
    exact hf (Complex.normSq_eq_zero.mp
      ((mul_eq_zero.mp (h s (Finsupp.mem_support_iff.mpr hf))).resolve_right hs))
  · by_cases hs : w s = 0
    · simp [hs]
    · simp [h s hs]

end Finsupp
