/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# The half-line integral `∫_{x > 0} x⁻¹/² (a + x)⁻¹ dx = π / √a`

For every positive real `a`,

`∫_{x > 0} (√x)⁻¹ * (a + x)⁻¹ dx = π / √a`.

Equivalently, `a⁻¹/² = π⁻¹ ∫_{x > 0} x⁻¹/² (a + x)⁻¹ dx`, which is the scalar case of the
Balakrishnan and Baaj–Julg integral formula for the inverse square root of a positive operator.
On `(0, ∞)` the integrand is nonnegative and equals the derivative of
`x ↦ (2 / √a) * arctan (√x / √a)`, which is continuous at `0⁺` with value `0` and tends to
`π / √a` at infinity, giving both integrability and the exact value of the integral.

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

private theorem hasDerivAt_inv_sqrt_mul_inv_add_primitive {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    HasDerivAt (fun t ↦ (2 / √a) * arctan (√t / √a)) ((√x)⁻¹ * (a + x)⁻¹) x := by
  have ha' : √a ≠ 0 := (sqrt_pos.2 ha).ne'
  have hx' : √x ≠ 0 := (sqrt_pos.2 hx).ne'
  refine ((((hasDerivAt_id x).sqrt hx.ne').div_const √a).arctan.const_mul (2 / √a)).congr_deriv ?_
  simp only [id]
  field_simp
  rw [sq_sqrt ha.le, sq_sqrt hx.le]

private theorem tendsto_inv_sqrt_mul_inv_add_primitive {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t ↦ (2 / √a) * arctan (√t / √a)) atTop (𝓝 (π / √a)) := by
  have hdiv : Tendsto (fun t : ℝ ↦ √t / √a) atTop atTop :=
    tendsto_sqrt_atTop.atTop_div_const (sqrt_pos.2 ha)
  have h := ((tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop).comp hdiv).const_mul
    (2 / √a)
  have hlim : 2 / √a * (π / 2) = π / √a := by ring
  simpa only [Function.comp_def, hlim] using h

/-- For `a > 0`, `x ↦ (√x)⁻¹ * (a + x)⁻¹` is integrable on `(0, ∞)`. -/
theorem integrableOn_Ioi_inv_sqrt_mul_inv_add {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ (√x)⁻¹ * (a + x)⁻¹) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg
    (Continuous.continuousWithinAt (by fun_prop))
    (fun _ hx ↦ hasDerivAt_inv_sqrt_mul_inv_add_primitive ha hx)
    (fun x hx ↦ by have : 0 < x := hx; positivity)
    (tendsto_inv_sqrt_mul_inv_add_primitive ha)

/-- **The inverse-square-root integral formula.** For every `a > 0`,
`∫ x in Ioi 0, (√x)⁻¹ * (a + x)⁻¹ = π / √a`. -/
theorem integral_Ioi_inv_sqrt_mul_inv_add {a : ℝ} (ha : 0 < a) :
    ∫ x in Ioi (0 : ℝ), (√x)⁻¹ * (a + x)⁻¹ = π / √a := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg
    (Continuous.continuousWithinAt (by fun_prop))
    (fun _ hx ↦ hasDerivAt_inv_sqrt_mul_inv_add_primitive ha hx)
    (fun x hx ↦ by have : 0 < x := hx; positivity)
    (tendsto_inv_sqrt_mul_inv_add_primitive ha)
  simpa using h

end TauCeti
