/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The half-line integral `∫_{x > 0} x⁻¹/² (a + x)⁻¹ dx = π / √a`

For every positive real `a`,

`∫_{x > 0} (√x)⁻¹ * (a + x)⁻¹ dx = π / √a`.

Equivalently, `a⁻¹/² = π⁻¹ ∫_{x > 0} x⁻¹/² (a + x)⁻¹ dx`, which is the scalar case of the
Balakrishnan and Baaj–Julg integral formula for the inverse square root of a positive operator.
Integrability follows from `Real.integrableOn_rpowIntegrandNeg` at `p = -1 / 2`, and the exact
value follows by substituting `x = u²` and scaling `u = √a * v` to reduce to
`integral_Ioi_inv_one_add_sq`.

## Main results

* `TauCeti.integrableOn_Ioi_inv_sqrt_mul_inv_add`: `(√x)⁻¹ * (a + x)⁻¹` is integrable on `(0, ∞)`
  for `a > 0`.
* `TauCeti.integral_Ioi_inv_sqrt_mul_inv_add`:
  `∫ x in Ioi 0, (√x)⁻¹ * (a + x)⁻¹ = π / √a` for `a > 0`.
-/

public section

open Filter MeasureTheory Real Set
open scoped Topology

namespace TauCeti

/-- For `a > 0`, `x ↦ (√x)⁻¹ * (a + x)⁻¹` is integrable on `(0, ∞)`. -/
theorem integrableOn_Ioi_inv_sqrt_mul_inv_add {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ (√x)⁻¹ * (a + x)⁻¹) (Ioi 0) := by
  refine (integrableOn_rpowIntegrandNeg (p := -1 / 2) (by norm_num) ha).congr_fun
    (fun x (hx : 0 < x) ↦ ?_) measurableSet_Ioi
  dsimp only [rpowIntegrandNeg]
  rw [add_comm, sqrt_eq_rpow, ← rpow_neg hx.le, ← neg_div]

/-- **The inverse-square-root integral formula.** For every `a > 0`,
`∫ x in Ioi 0, (√x)⁻¹ * (a + x)⁻¹ = π / √a`. -/
theorem integral_Ioi_inv_sqrt_mul_inv_add {a : ℝ} (ha : 0 < a) :
    ∫ x in Ioi (0 : ℝ), (√x)⁻¹ * (a + x)⁻¹ = π / √a := by
  have hsq : ∫ x in Ioi (0 : ℝ), (√x)⁻¹ * (a + x)⁻¹ =
      2 * ∫ u in Ioi (0 : ℝ), (a + u ^ 2)⁻¹ := by
    rw [← integral_comp_rpow_Ioi_of_pos (g := fun x ↦ (√x)⁻¹ * (a + x)⁻¹) zero_lt_two,
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) ↦ ?_
    norm_num [rpow_two, sqrt_sq hu.le, smul_eq_mul]
    rw [mul_assoc, ← mul_assoc u, mul_inv_cancel₀ hu.ne', one_mul]
  have hscale : ∫ u in Ioi (0 : ℝ), (a + u ^ 2)⁻¹ =
      √a * (a⁻¹ * ∫ v in Ioi (0 : ℝ), (1 + v ^ 2)⁻¹) := by
    have h1 := integral_comp_mul_left_Ioi' (fun u : ℝ ↦ (a + u ^ 2)⁻¹) 0 (sqrt_pos.2 ha)
    rw [mul_zero, smul_eq_mul] at h1
    rw [← h1, ← mul_assoc, ← integral_const_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ ↦ ?_
    rw [mul_pow, sq_sqrt ha.le, ← mul_one_add, mul_inv, ← mul_assoc]
  rw [hsq, hscale, integral_Ioi_inv_one_add_sq, arctan_zero, sub_zero]
  have hsqa : √a ≠ 0 := (sqrt_pos.2 ha).ne'
  field_simp
  rw [sq_sqrt ha.le]

end TauCeti
