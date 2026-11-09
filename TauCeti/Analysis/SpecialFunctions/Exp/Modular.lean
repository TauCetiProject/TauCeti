/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import TauCeti.Analysis.SpecialFunctions.Sqrt

/-!
# The exponential potential dominates the modular `√(1 + t²) - 1`

The convex potential `exp (2t) - 1 - 2t` is nonnegative and vanishes to second order at `0`, like
the modular `√(1 + t²) - 1`. For positive `t` it grows exponentially, but for negative `t` only
linearly, as does the modular. This file records the comparison

`√(1 + t²) - 1 ≤ exp (2t) - 1 - 2t`

(`Real.sqrt_one_add_sq_sub_one_le_exp_two_mul_sub_one_sub_two_mul`), which turns a bound on the
potential into a bound on a quantity comparable to `min (t², |t|)`. It is the pointwise input to
coercivity estimates for functionals with this potential, such as Taubes's functional for planar
vortices.

## Main results

* `Real.exp_two_mul_sub_one_sub_two_mul_nonneg`: for every real `t`, `0 ≤ exp (2t) - 1 - 2t`.
* `Real.convexOn_exp_two_mul_sub_one_sub_two_mul`: the potential `exp (2t) - 1 - 2t` is convex.
* `Real.sqrt_one_add_sq_sub_one_le_exp_two_mul_sub_one_sub_two_mul`: for every real `t`,
  `√(1 + t²) - 1 ≤ exp (2t) - 1 - 2t`.
-/

public section

namespace Real

/-- The potential `exp (2t) - 1 - 2t` is nonnegative. -/
theorem exp_two_mul_sub_one_sub_two_mul_nonneg (t : ℝ) : 0 ≤ exp (2 * t) - 1 - 2 * t := by
  linarith [add_one_le_exp (2 * t)]

/-- The potential `exp (2t) - 1 - 2t` is convex. -/
theorem convexOn_exp_two_mul_sub_one_sub_two_mul :
    ConvexOn ℝ Set.univ fun t : ℝ ↦ exp (2 * t) - 1 - 2 * t := by
  have hlin := (LinearMap.mulLeft ℝ (2 : ℝ)).concaveOn (convex_univ : Convex ℝ (Set.univ : Set ℝ))
  simpa only [Set.preimage_univ, Pi.sub_def, Function.comp_def, LinearMap.mulLeft_apply] using
    ((convexOn_exp.comp_linearMap (LinearMap.mulLeft ℝ (2 : ℝ))).sub
      (concaveOn_const (1 : ℝ) convex_univ)).sub hlin

/-- The potential `exp (2t) - 1 - 2t` dominates the modular `√(1 + t²) - 1`. -/
theorem sqrt_one_add_sq_sub_one_le_exp_two_mul_sub_one_sub_two_mul (t : ℝ) :
    √(1 + t ^ 2) - 1 ≤ exp (2 * t) - 1 - 2 * t := by
  have hsq := sqrt_one_add_sq_sub_one_le_sq_div_two t
  rcases le_total 0 t with ht | ht
  · have := quadratic_le_exp_of_nonneg (by linarith : 0 ≤ 2 * t)
    nlinarith
  rcases le_total (-1) t with ht1 | ht1
  · -- For `-1 ≤ t ≤ 0`, `(1 + 2t/3)³ ≤ exp (2t)`.
    have h := one_sub_div_pow_le_exp_neg (n := 3) (t := -(2 * t)) (by push_cast; linarith)
    rw [neg_neg] at h
    have ht3 : 0 ≤ t ^ 2 * (t + 1) := mul_nonneg (sq_nonneg t) (by linarith)
    nlinarith
  · -- For `t ≤ -1`, `exp (2t) - 1 - 2t ≥ -t - (1 + t) ≥ |t| ≥ √(1 + t²) - 1`.
    have habs := sqrt_one_add_sq_sub_one_le_abs t
    rw [abs_of_nonpos ht] at habs
    nlinarith [exp_pos (2 * t)]

end Real

end
