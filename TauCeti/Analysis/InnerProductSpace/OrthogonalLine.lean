/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearIsometry

/-!
# Covectors on a line and its orthogonal hyperplane

Let `e` be a unit vector of a real inner product space and `v` a vector of the orthogonal
hyperplane `(ℝ ∙ e)ᗮ` with `‖v‖ ≤ 1`. By Pythagoras in orthogonal line coordinates
(`TauCeti.norm_add_smul_sq`), the vectors `±√(1 - ‖v‖²) e - v` have norm one, so every covector
`L` satisfies `√(1 - ‖v‖²) |L e| - L v ≤ ‖L‖`. This pointwise bound is what lets the variation
of a function along `e`, weighted by `√(1 - ‖v‖²)`, be combined with its variation in the
transverse direction `-v` without exceeding its total variation.

## Main results

* `TauCeti.sqrt_mul_abs_apply_sub_apply_le`: `√(1 - ‖v‖²) |L e| - L v ≤ ‖L‖` for a covector `L`,
  a unit vector `e` and `v ⊥ e` with `‖v‖ ≤ 1`.
-/

public section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A covector `L` and a vector `v ⊥ e` with `‖v‖ ≤ 1` satisfy
`√(1 - ‖v‖²) |L e| - L v ≤ ‖L‖`: the left side is `L` applied to `±√(1 - ‖v‖²) e - v`, a vector
of norm one by `TauCeti.norm_add_smul_sq`. -/
theorem sqrt_mul_abs_apply_sub_apply_le (e : E) (he : ‖e‖ = 1) (L : E →L[ℝ] ℝ)
    {v : (ℝ ∙ e)ᗮ} (hv : ‖v‖ ≤ 1) :
    √(1 - ‖v‖ ^ 2) * |L e| - L v ≤ ‖L‖ := by
  have key (σ : ℝ) (hσ : σ ^ 2 = 1) : σ * √(1 - ‖v‖ ^ 2) * L e - L v ≤ ‖L‖ := by
    set z : E := ((-v : (ℝ ∙ e)ᗮ) : E) + (σ * √(1 - ‖v‖ ^ 2)) • e
    have hz : ‖z‖ ^ 2 = 1 := by
      rw [norm_add_smul_sq e he, norm_neg, mul_pow, hσ,
        Real.sq_sqrt (by nlinarith [norm_nonneg v])]
      ring
    calc σ * √(1 - ‖v‖ ^ 2) * L e - L v = L z := by simp [z, sub_eq_neg_add]
      _ ≤ ‖L‖ * 1 := (le_abs_self _).trans (L.le_opNorm_of_le (by nlinarith [norm_nonneg z]))
      _ = ‖L‖ := mul_one _
  rcases le_total 0 (L e) with h | h
  · simpa [abs_of_nonneg h] using key 1 (by norm_num)
  · simpa [abs_of_nonpos h] using key (-1) (by norm_num)

end TauCeti
