/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Sqrt
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
-/

public section

namespace Real

/-- The potential `exp (2t) - 1 - 2t` dominates the modular `√(1 + t²) - 1`. -/
theorem sqrt_one_add_sq_sub_one_le_exp_two_mul_sub_one_sub_two_mul (t : ℝ) :
    √(1 + t ^ 2) - 1 ≤ exp (2 * t) - 1 - 2 * t := by
  have hsq : √(1 + t ^ 2) ≤ 1 + t ^ 2 / 2 :=
    sqrt_le_iff.mpr ⟨by positivity, by nlinarith [sq_nonneg (t ^ 2)]⟩
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
