/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The slope of the real exponential at zero

This file records the parameterized right-sided slope limit for `t ↦ exp (a * t)`, together with
the uniform bound on these slopes for a decaying exponential. These are small shared calculus facts
used by semigroup generator shifts and resolvent calculations.

## Main results

* `TauCeti.tendsto_exp_mul_sub_one_div`: `(exp (a * t) - 1) / t` tends to `a` as `t → 0⁺`.
* `TauCeti.abs_exp_mul_sub_one_div_le`: for `a ≤ 0` and `t > 0`, the slope
  `(exp (a * t) - 1) / t` has absolute value at most `-a`.
-/

public section

namespace TauCeti

open Filter

/-- The right-sided difference quotient of `t ↦ exp (a * t)` at zero tends to `a`. -/
theorem tendsto_exp_mul_sub_one_div (a : ℝ) :
    Tendsto (fun t : ℝ => (Real.exp (a * t) - 1) / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds a) := by
  have hderiv : HasDerivAt (fun t : ℝ => Real.exp (a * t)) a 0 := by
    convert ((hasDerivAt_id (x := (0 : ℝ))).const_mul a).exp using 1 <;> simp
  simpa only [zero_add, mul_zero, Real.exp_zero, smul_eq_mul, div_eq_mul_inv,
    mul_comm] using hderiv.tendsto_slope_zero_right

/-- For a decaying exponential `t ↦ exp (a * t)`, every right-sided slope at zero is bounded by
the absolute value `-a` of its derivative there. -/
theorem abs_exp_mul_sub_one_div_le {a t : ℝ} (ha : a ≤ 0) (ht : 0 < t) :
    |(Real.exp (a * t) - 1) / t| ≤ -a := by
  have hat : a * t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha ht.le
  rw [abs_div, abs_of_pos ht, abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr hat)),
    div_le_iff₀ ht]
  linarith [Real.add_one_le_exp (a * t)]

end TauCeti

end
