/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Integrals.SqrtQuadratic

/-!
# The integral of `√(1 - t²) / (c + r t)`

For `0 < r ≤ c`,

`∫_{-1}^{1} √(1 - t²) / (c + r t) dt = π (c - √(c² - r²)) / r²`.

At `r = c` the denominator vanishes at `t = -1` and the integrand is unbounded there, but it
remains integrable. Both facts are transported along the substitution `x = r t + c` from the
quadrature of `√((x - a) (b - x)) / x` with `a = c - r` and `b = c + r` in
`TauCeti.Analysis.SpecialFunctions.Integrals.SqrtQuadratic`, which allows the lower root `a = 0`.

Integrals of this shape compute the inverse moment of a semicircle law.

## Main results

* `TauCeti.integrableOn_sqrt_one_sub_sq_mul_inv`: the integrand is integrable on `(-1, 1]`;
* `TauCeti.integral_sqrt_one_sub_sq_mul_inv`: the value of the integral.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press, 2010, §2.1.1.
-/

public section

open MeasureTheory Real Set

namespace TauCeti

/-- Under `x = r t + c`, `√(1 - t²) / (c + r t)` is `r⁻¹ √((x - (c - r)) (c + r - x)) / x`. -/
private theorem sqrt_one_sub_sq_mul_inv_eq {c r : ℝ} (hr : 0 < r) :
    (fun t ↦ √(1 - t ^ 2) * (c + r * t)⁻¹) =
      fun t ↦ r⁻¹ * (√((r * t + c - (c - r)) * (c + r - (r * t + c))) / (r * t + c)) := by
  ext t
  rw [show (r * t + c - (c - r)) * (c + r - (r * t + c)) = r ^ 2 * (1 - t ^ 2) by ring,
    sqrt_mul (sq_nonneg r), sqrt_sq hr.le, add_comm (r * t), mul_div_assoc,
    inv_mul_cancel_left₀ hr.ne', div_eq_mul_inv]

/-- The integrand `√(1 - t²) / (c + r t)` is integrable on `(-1, 1]` when `0 < r ≤ c`. -/
theorem integrableOn_sqrt_one_sub_sq_mul_inv {c r : ℝ} (hr : 0 < r) (hrc : r ≤ c) :
    IntegrableOn (fun t ↦ √(1 - t ^ 2) * (c + r * t)⁻¹) (Ioc (-1) 1) := by
  have h := (((intervalIntegrable_sqrt_mul_sub_mul_sub_div (a := c - r) (b := c + r)
    (by linarith) (by linarith)).comp_add_right c).comp_mul_left (c := r)).const_mul r⁻¹
  rw [show (c - r - c) / r = -1 by field_simp; ring, show (c + r - c) / r = 1 by field_simp; ring,
    intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at h
  rw [sqrt_one_sub_sq_mul_inv_eq hr]
  simpa only [add_sub_cancel_right, sub_add_cancel] using h

/-- For `0 < r ≤ c`, `∫_{-1}^{1} √(1 - t²) / (c + r t) dt = π (c - √(c² - r²)) / r²`. -/
theorem integral_sqrt_one_sub_sq_mul_inv {c r : ℝ} (hr : 0 < r) (hrc : r ≤ c) :
    ∫ t in -1..1, √(1 - t ^ 2) * (c + r * t)⁻¹ = π * (c - √(c ^ 2 - r ^ 2)) / r ^ 2 := by
  rw [sqrt_one_sub_sq_mul_inv_eq hr, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_add (fun x ↦ √((x - (c - r)) * (c + r - x)) / x) hr.ne',
    show r * -1 + c = c - r by ring, show r * 1 + c = c + r by ring,
    integral_sqrt_mul_sub_mul_sub_div (sub_nonneg.2 hrc) (by linarith),
    show (c - r) * (c + r) = c ^ 2 - r ^ 2 by ring, smul_eq_mul]
  field_simp
  ring

end TauCeti
