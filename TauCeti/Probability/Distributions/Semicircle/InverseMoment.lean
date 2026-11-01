/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Semicircle.LocationScale
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# The inverse moment of a semicircle law

When the semicircle law with centre `a` and variance `v` is carried by `[0, ∞)`, that is when
`2 * √v ≤ a`, the function `x ↦ x⁻¹` is integrable against it, and for `0 < v`

`∫ x⁻¹ d(semicircleReal a v) = (a - √(a² - 4v)) / (2v)`.

At the boundary case `a = 2 * √v` the support touches `0` and `x⁻¹` is unbounded, but it remains
integrable. These are the facts needed to normalize the Marchenko–Pastur law, whose absolutely
continuous part is `x⁻¹` times a semicircle law.

The integral is computed on the unit-radius law by the fundamental theorem of calculus: for
`0 < r ≤ c` and `|t| < 1`, a primitive of `√(1 - t²) / (c + r t)` is
`(c arcsin t + r √(1 - t²) - √(c² - r²) arcsin ((c t + r) / (c + r t))) / r²`.

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

/-- The arcsine part of the primitive of `√(1 - t²) / (c + r t)`. It vanishes when `c = r`. -/
private theorem hasDerivAt_sqrt_mul_arcsin {c r t : ℝ} (hr : 0 < r) (hrc : r ≤ c)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t ↦ √(c ^ 2 - r ^ 2) * arcsin ((c * t + r) / (c + r * t)))
      ((c ^ 2 - r ^ 2) / ((c + r * t) * √(1 - t ^ 2))) t := by
  rcases hrc.eq_or_lt with rfl | hrc
  · simpa using hasDerivAt_const t (0 : ℝ)
  have hq : 0 < c + r * t := by nlinarith [ht.1]
  have hs : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hd2 : √(c ^ 2 - r ^ 2) ^ 2 = c ^ 2 - r ^ 2 := sq_sqrt (by nlinarith)
  have hd : 0 < √(c ^ 2 - r ^ 2) := sqrt_pos.2 (by nlinarith)
  have hst : 0 < √(1 - t ^ 2) := sqrt_pos.2 hs
  have hg : 1 - ((c * t + r) / (c + r * t)) ^ 2 =
      (√(c ^ 2 - r ^ 2) * √(1 - t ^ 2) / (c + r * t)) ^ 2 := by
    rw [div_pow, div_pow, mul_pow, hd2, sq_sqrt hs.le, eq_div_iff (by positivity), sub_mul,
      div_mul_cancel₀ _ (by positivity)]
    ring
  have hg1 : 0 < 1 - ((c * t + r) / (c + r * t)) ^ 2 := by
    rw [hg]
    positivity
  have hinner : HasDerivAt (fun t ↦ (c * t + r) / (c + r * t))
      ((c ^ 2 - r ^ 2) / (c + r * t) ^ 2) t := by
    convert (((hasDerivAt_id' t).const_mul c).add_const r).fun_div
      (((hasDerivAt_id' t).const_mul r).const_add c) hq.ne' using 1
    ring
  have harcsin : HasDerivAt (fun t ↦ arcsin ((c * t + r) / (c + r * t)))
      (1 / √(1 - ((c * t + r) / (c + r * t)) ^ 2) * ((c ^ 2 - r ^ 2) / (c + r * t) ^ 2)) t :=
    (hasDerivAt_arcsin (by nlinarith) (by nlinarith)).comp t hinner
  convert harcsin.const_mul √(c ^ 2 - r ^ 2) using 1
  rw [hg, sqrt_sq (by positivity)]
  field_simp

/-- The derivative of the primitive of `√(1 - t²) / (c + r t)`, scaled by `r²`. -/
private theorem hasDerivAt_primitive {c r t : ℝ} (hr : 0 < r) (hrc : r ≤ c)
    (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t ↦ c * arcsin t + r * √(1 - t ^ 2) -
        √(c ^ 2 - r ^ 2) * arcsin ((c * t + r) / (c + r * t)))
      (r ^ 2 * (√(1 - t ^ 2) * (c + r * t)⁻¹)) t := by
  have hq : 0 < c + r * t := by nlinarith [ht.1]
  have hs : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  have hst : 0 < √(1 - t ^ 2) := sqrt_pos.2 hs
  have h1 := (hasDerivAt_arcsin (x := t) (by linarith [ht.1]) (by linarith [ht.2])).const_mul c
  have h0 : HasDerivAt (fun t ↦ 1 - t ^ 2) (-(2 * t)) t := by
    simpa using (hasDerivAt_pow 2 t).const_sub 1
  have h2 := (HasDerivAt.sqrt h0 hs.ne').const_mul r
  convert (h1.add h2).sub (hasDerivAt_sqrt_mul_arcsin hr hrc ht) using 1
  field_simp
  rw [sq_sqrt hs.le]
  ring

/-- The primitive of `√(1 - t²) / (c + r t)` is continuous on `[-1, 1]`. -/
private theorem continuousOn_primitive {c r : ℝ} (hr : 0 < r) (hrc : r ≤ c) :
    ContinuousOn (fun t ↦ c * arcsin t + r * √(1 - t ^ 2) -
        √(c ^ 2 - r ^ 2) * arcsin ((c * t + r) / (c + r * t))) (Icc (-1) 1) := by
  refine (Continuous.continuousOn (by fun_prop)).sub ?_
  rcases hrc.eq_or_lt with rfl | hrc
  · simpa using continuousOn_const
  refine ContinuousOn.mul continuousOn_const (continuous_arcsin.comp_continuousOn ?_)
  exact (Continuous.continuousOn (by fun_prop)).div (Continuous.continuousOn (by fun_prop))
    fun t ht ↦ by nlinarith [ht.1]

/-- The integrand `√(1 - t²) / (c + r t)` is integrable on `(-1, 1]` when `0 < r ≤ c`. -/
private theorem integrableOn_sqrt_mul_inv {c r : ℝ} (hr : 0 < r) (hrc : r ≤ c) :
    IntegrableOn (fun t ↦ √(1 - t ^ 2) * (c + r * t)⁻¹) (Ioc (-1) 1) := by
  have h := intervalIntegral.integrableOn_deriv_of_nonneg (continuousOn_primitive hr hrc)
    (fun t ht ↦ hasDerivAt_primitive hr hrc ht) fun t ht ↦ by
      have : 0 < c + r * t := by nlinarith [ht.1]
      positivity
  refine IntegrableOn.congr_fun (h.const_mul (r ^ 2)⁻¹) (fun t _ ↦ ?_) measurableSet_Ioc
  field_simp

/-- For `0 < r ≤ c`, `∫_{-1}^{1} √(1 - t²) / (c + r t) dt = π (c - √(c² - r²)) / r²`. -/
private theorem integral_sqrt_mul_inv {c r : ℝ} (hr : 0 < r) (hrc : r ≤ c) :
    ∫ t in -1..1, √(1 - t ^ 2) * (c + r * t)⁻¹ = π * (c - √(c ^ 2 - r ^ 2)) / r ^ 2 := by
  have hint : IntervalIntegrable (fun t ↦ r ^ 2 * (√(1 - t ^ 2) * (c + r * t)⁻¹)) volume
      (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).2
      ((integrableOn_sqrt_mul_inv hr hrc).const_mul _)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num)
    (continuousOn_primitive hr hrc) (fun t ht ↦ hasDerivAt_primitive hr hrc ht) hint
  rw [intervalIntegral.integral_const_mul] at h
  have hleft : √(c ^ 2 - r ^ 2) * arcsin ((c * -1 + r) / (c + r * -1)) =
      -(√(c ^ 2 - r ^ 2) * (π / 2)) := by
    rcases hrc.eq_or_lt with rfl | hrc
    · simp
    rw [show (c * -1 + r) / (c + r * -1) = -1 by
      rw [div_eq_iff (by linarith)]
      ring, arcsin_neg_one]
    ring
  have hright : (c * 1 + r) / (c + r * 1) = 1 := by
    rw [div_eq_one_iff_eq (by linarith)]
    ring
  simp only [hright, hleft, arcsin_one, arcsin_neg_one, one_pow, neg_one_sq, sub_self,
    sqrt_zero, mul_zero, add_zero] at h
  rw [eq_div_iff (by positivity)]
  linear_combination h

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
    (IntegrableOn.congr_fun ((integrableOn_sqrt_mul_inv hr h).const_mul (2 / π))
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
  rw [integral_sqrt_mul_inv hr h, mul_pow, sq_sqrt v.coe_nonneg, show (2 : ℝ) ^ 2 = 4 by norm_num]
  field_simp
  ring

end TauCeti.Probability
