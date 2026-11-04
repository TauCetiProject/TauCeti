/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Semicircle.LocationScale
import TauCeti.Analysis.SpecialFunctions.Integrals.SqrtOneSubSqDivLinear

/-!
# The inverse moment of a semicircle law

When the semicircle law with centre `a` and variance `v` is carried by `[0, ∞)`, that is when
`2 * √v ≤ a`, the function `x ↦ x⁻¹` is integrable against it, and for `0 < v`

`∫ x⁻¹ d(semicircleReal a v) = (a - √(a² - 4v)) / (2v)`.

At the boundary case `a = 2 * √v` the support touches `0` and `x⁻¹` is unbounded, but it remains
integrable. These are the facts needed to normalize the Marchenko–Pastur law, whose absolutely
continuous part is `x⁻¹` times a semicircle law.

On the unit-radius law the integral becomes `∫_{-1}^{1} √(1 - t²) / (c + r t) dt` with
`c = a` and `r = 2√v`, which `TauCeti.integral_sqrt_one_sub_sq_mul_inv` evaluates as
`π (c - √(c² - r²)) / r²`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*,
  Cambridge University Press, 2010, §2.1.1.
* Z. D. Bai, J. W. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*,
  2nd ed., Springer, 2010, §3.1.
-/

public section

noncomputable section

open MeasureTheory Real Set
open scoped NNReal

namespace TauCeti.Probability

/-- The function `x ↦ x⁻¹` is integrable against a semicircle law carried by `[0, ∞)`. At
`a = 2 * √v` it is unbounded near the lower edge `0`, but still integrable. -/
theorem integrable_inv_semicircleReal {a : ℝ} {v : ℝ≥0} (h : 2 * √v ≤ a) :
    Integrable (fun x ↦ x⁻¹) (semicircleReal a v) := by
  rcases eq_zero_or_pos v with rfl | hv
  · simpa using integrable_dirac (by simp)
  have hr : 0 < 2 * √v := by positivity
  rw [semicircleReal_def, integrable_map_measure measurable_inv.aestronglyMeasurable
    (by fun_prop), semicircleMeasure_eq_withDensity,
    integrable_withDensity_iff measurable_semicirclePDF (.of_forall fun _ ↦ by simp)]
  refine IntegrableOn.integrable_of_forall_notMem_eq_zero
    (IntegrableOn.congr_fun ((integrableOn_sqrt_one_sub_sq_mul_inv hr h).const_mul (2 / π))
      (fun t _ ↦ ?_) measurableSet_Ioc) fun t ht ↦ ?_
  · rw [Function.comp_apply, semicirclePDF_apply,
      ENNReal.toReal_ofReal (semicirclePDFReal_nonneg t), semicirclePDFReal_apply]
    ring
  · have ht' : 1 - t ^ 2 ≤ 0 := by
      simp only [mem_Ioc, not_and_or, not_lt, not_le] at ht
      rcases ht with ht | ht <;> nlinarith
    simp [semicirclePDFReal_apply, sqrt_eq_zero_of_nonpos ht']

/-- The inverse moment of a semicircle law carried by `[0, ∞)`:
`∫ x⁻¹ d(semicircleReal a v) = (a - √(a² - 4v)) / (2v)` for `0 < v` and `2 * √v ≤ a`. -/
theorem integral_inv_semicircleReal {a : ℝ} {v : ℝ≥0} (hv : 0 < v) (h : 2 * √v ≤ a) :
    ∫ x, x⁻¹ ∂semicircleReal a v = (a - √(a ^ 2 - 4 * v)) / (2 * v) := by
  have hr : 0 < 2 * √v := by positivity
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  rw [semicircleReal_def, integral_map (by fun_prop) measurable_inv.aestronglyMeasurable,
    integral_semicircleMeasure_eq_intervalIntegral]
  simp only [smul_eq_mul]
  have h4 : (2 : ℝ) ^ 2 = 4 := by norm_num
  rw [integral_sqrt_one_sub_sq_mul_inv hr h, mul_pow, sq_sqrt v.coe_nonneg, h4]
  field_simp
  ring

end TauCeti.Probability
