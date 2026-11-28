/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Chords from `1` on the unit circle

* `Complex.norm_exp_ofReal_mul_I_sub_one_of_mem_Icc` removes the absolute value from
  `Complex.norm_exp_I_mul_ofReal_sub_one` for angles in `[0, 2π]`.
* `Complex.exp_ofReal_mul_I_ne_one_of_mem_Ioo` uses positivity of that chord length to exclude
  `1` for angles in `(0, 2π)`.
-/

public section

namespace Complex

open scoped Real

/-- For `0 ≤ θ ≤ 2π`, the chord from `1` to `exp (θ i)` has length `2 sin (θ / 2)`. -/
theorem norm_exp_ofReal_mul_I_sub_one_of_mem_Icc {θ : ℝ} (hθ : θ ∈ Set.Icc 0 (2 * π)) :
    ‖exp (θ * I) - 1‖ = 2 * Real.sin (θ / 2) := by
  have hs : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  rw [mul_comm _ I, norm_exp_I_mul_ofReal_sub_one, Real.norm_of_nonneg (by positivity)]

/-- For `0 < θ < 2π`, the point `exp (θ i)` is not `1`. -/
theorem exp_ofReal_mul_I_ne_one_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (2 * π)) :
    exp (θ * I) ≠ 1 := by
  have hs : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  refine sub_ne_zero.mp (norm_pos_iff.mp ?_)
  rw [norm_exp_ofReal_mul_I_sub_one_of_mem_Icc (Set.Ioo_subset_Icc_self hθ)]
  positivity

end Complex
