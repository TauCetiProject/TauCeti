/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.SpecialFunctions.Beta.Basic

/-!
# The half-line integral `∫_{x > 0} x⁻¹/² (a + x)⁻¹ dx = π / √a`

For every positive real `a`,

`∫_{x > 0} (√x)⁻¹ * (a + x)⁻¹ dx = π / √a`.

Equivalently, `a⁻¹/² = π⁻¹ ∫_{x > 0} x⁻¹/² (a + x)⁻¹ dx`, which is the scalar case of the
Balakrishnan and Baaj–Julg integral formula for the inverse square root of a positive operator.
Integrability and the exact value follow from `TauCeti.integrableOn_rpow_div_add` and
`TauCeti.integral_rpow_div_add` at `s = 1 / 2`.

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
  refine (integrableOn_rpow_div_add (1 / 2) a (by norm_num) (by norm_num) ha).congr_fun
    (fun x (hx : 0 < x) ↦ ?_) measurableSet_Ioi
  dsimp only
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, rpow_neg hx.le, ← sqrt_eq_rpow,
    div_eq_mul_inv, add_comm]

/-- **The inverse-square-root integral formula.** For every `a > 0`,
`∫ x in Ioi 0, (√x)⁻¹ * (a + x)⁻¹ = π / √a`. -/
theorem integral_Ioi_inv_sqrt_mul_inv_add {a : ℝ} (ha : 0 < a) :
    ∫ x in Ioi (0 : ℝ), (√x)⁻¹ * (a + x)⁻¹ = π / √a := by
  calc
    ∫ x in Ioi (0 : ℝ), (√x)⁻¹ * (a + x)⁻¹
      = ∫ x in Ioi (0 : ℝ), x ^ ((1 / 2 : ℝ) - 1) / (x + a) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) ↦ ?_
        rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, rpow_neg hx.le, ← sqrt_eq_rpow,
          div_eq_mul_inv, add_comm]
    _ = a ^ ((1 / 2 : ℝ) - 1) * (π / sin (π * (1 / 2))) :=
        integral_rpow_div_add (1 / 2) a (by norm_num) (by norm_num) ha
    _ = π / √a := by
        rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, rpow_neg ha.le, ← sqrt_eq_rpow,
          mul_one_div, sin_pi_div_two, div_one, mul_comm, div_eq_mul_inv]

end TauCeti
