/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.Algebra.Field.LinearFractional

/-!
# The beta weight under the half-line chart

The chart `u ↦ u / (1 - u)` takes the complex second-beta weight to the first-beta
weight. Its positive Jacobian matches the substitution API in `Analysis.Calculus.RealCharts`.
-/

public section

namespace Complex

/-- Under the chart `u ↦ u / (1 - u)` of `(0, 1)` onto `(0, ∞)`, the Mellin integrand of
`(1 + t)^{-a}` at `s`, including the positive Jacobian, becomes the beta weight with
parameters `s` and `a - s`. -/
theorem inv_sq_smul_div_cpow_smul_one_add_cpow (s a : ℂ) {u : ℝ}
    (hu : u ∈ Set.Ioo 0 1) :
    ((1 - u) ^ 2)⁻¹ •
        (((u / (1 - u) : ℝ) : ℂ) ^ (s - 1) •
          (1 + ((u / (1 - u) : ℝ) : ℂ)) ^ (-a)) =
      (u : ℂ) ^ (s - 1) * (1 - (u : ℂ)) ^ (a - s - 1) := by
  have h1u : 0 < 1 - u := sub_pos.mpr hu.2
  have hd : ((1 - u : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr h1u.ne'
  have hbase : 1 + ((u / (1 - u) : ℝ) : ℂ) = ((1 - u : ℝ) : ℂ)⁻¹ := by
    exact_mod_cast TauCeti.one_add_div_one_sub h1u.ne'
  have hsq : (((1 - u : ℝ) : ℂ) ^ 2)⁻¹ = ((1 - u : ℝ) : ℂ) ^ (-2 : ℂ) := by
    rw [cpow_neg, show (2 : ℂ) = (2 : ℕ) by norm_num, cpow_natCast]
  rw [real_smul, smul_eq_mul, hbase, ofReal_inv, ofReal_pow, ofReal_div,
    div_cpow_ofReal_nonneg hu.1.le h1u.le, inv_cpow_ofReal_nonneg h1u.le,
    hsq, div_eq_mul_inv, ← cpow_neg, ← cpow_neg, neg_neg]
  calc
    _ = (u : ℂ) ^ (s - 1) *
        (((1 - u : ℝ) : ℂ) ^ (-2 : ℂ) * ((1 - u : ℝ) : ℂ) ^ (-(s - 1)) *
          ((1 - u : ℝ) : ℂ) ^ a) := by ring
    _ = _ := by
      rw [← cpow_add _ _ hd, ← cpow_add _ _ hd]
      congr 2
      · push_cast
        ring
      · ring

end Complex
