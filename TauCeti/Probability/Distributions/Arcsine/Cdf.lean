/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Arcsine.PDF
public import Mathlib.Probability.CDF
import TauCeti.Probability.Cdf
import TauCeti.Probability.Distributions.Beta.Cdf
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The arcsine cumulative distribution function

The arcsine cdf is `2 / π * arcsin (√x)`. Mathlib's totalizations of square root and
arcsine give the correct zero and one extensions outside the unit interval.
On the open unit interval its derivative is the elementary arcsine density.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley, 1995, Chapter 25.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

/-- The arcsine cdf has the elementary arcsine density as its interior derivative. -/
theorem hasDerivAt_cdf_arcsineMeasure {x : ℝ} (hx : x ∈ Ioo 0 1) :
    HasDerivAt (cdf arcsineMeasure) (arcsinePDFReal x) x := by
  have hd := hasDerivAt_regularizedIncompleteBeta (a := 1 / 2) (b := 1 / 2)
    (by norm_num) (by norm_num) hx.1 hx.2
  convert hd using 1
  · funext y
    rw [arcsineMeasure_eq_betaMeasure, cdf_betaMeasure_eq (by norm_num) (by norm_num)]
  · rw [arcsinePDFReal_eq_betaPDFReal, betaPDFReal,
      ite_eq_left ⟨hx.1, hx.2⟩]
    ring

private theorem hasDerivAt_arcsineCDF {x : ℝ} (hx : x ∈ Ioo 0 1) :
    HasDerivAt (fun y : ℝ ↦ 2 / π * arcsin (√y)) (arcsinePDFReal x) x := by
  have hsq : √x < 1 := by simpa using sqrt_lt_sqrt hx.1.le hx.2
  convert ((hasDerivAt_arcsin (by linarith [sqrt_nonneg x]) hsq.ne).comp x
    (hasDerivAt_sqrt hx.1.ne')).const_mul (2 / π) using 1
  · exact funext fun _ ↦ rfl
  · rw [arcsinePDFReal_def, ite_eq_left hx, sq_sqrt hx.1.le, sqrt_mul hx.1.le]
    ring

/-- The arcsine cdf, with its zero and one extensions supplied by `sqrt` and `arcsin`. -/
theorem cdf_arcsineMeasure_eq (x : ℝ) :
    cdf arcsineMeasure x = 2 / π * arcsin (√x) := by
  have hc := Measure.continuous_cdf_of_noAtoms arcsineMeasure
  have hg : Continuous (fun y : ℝ ↦ 2 / π * arcsin (√y)) := by fun_prop
  have hzero : cdf arcsineMeasure 0 = 0 := by
    rw [arcsineMeasure_eq_betaMeasure, cdf_betaMeasure_eq (by norm_num) (by norm_num)]
    exact regularizedIncompleteBeta_eq_zero_of_nonpos (by norm_num) _ le_rfl
  rcases le_or_gt x 0 with hx | hx
  · rw [sqrt_eq_zero_of_nonpos hx, arcsin_zero, mul_zero]
    exact le_antisymm ((monotone_cdf arcsineMeasure hx).trans_eq hzero)
      (cdf_nonneg arcsineMeasure x)
  rcases le_or_gt 1 x with hx₁ | hx₁
  · rw [arcsin_of_one_le (one_le_sqrt.mpr hx₁)]
    have hone : cdf arcsineMeasure x = 1 := by
      rw [arcsineMeasure_eq_betaMeasure, cdf_betaMeasure_eq (by norm_num) (by norm_num)]
      exact regularizedIncompleteBeta_eq_one_of_one_le (by norm_num) (by norm_num) hx₁
    rw [hone]
    field_simp
  have hd : ∀ y ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun y ↦ cdf arcsineMeasure y - 2 / π * arcsin (√y)) 0 y := by
    intro y hy
    convert (hasDerivAt_cdf_arcsineMeasure hy).sub (hasDerivAt_arcsineCDF hy) using 1
    exact (sub_self _).symm
  have heq : EqOn (fun y ↦ cdf arcsineMeasure y - 2 / π * arcsin (√y))
      (fun _ ↦ cdf arcsineMeasure x - 2 / π * arcsin (√x)) (Ioo 0 1) := fun y hy ↦
    isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (0 : ℝ) 1).isPreconnected
      (fun y hy ↦ (hd y hy).differentiableAt.differentiableWithinAt)
      (fun y hy ↦ (hd y hy).deriv) hy ⟨hx, hx₁⟩
  have hmem : (0 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by simp
  have heq0 := heq.closure (hc.sub hg) continuous_const hmem
  simpa [hzero, sub_eq_zero] using heq0.symm

/-- The arcsine cdf vanishes at and below the lower support endpoint. -/
@[simp]
theorem cdf_arcsineMeasure_of_nonpos {x : ℝ} (hx : x ≤ 0) : cdf arcsineMeasure x = 0 := by
  simp [cdf_arcsineMeasure_eq, sqrt_eq_zero_of_nonpos hx]

/-- The arcsine cdf is one at and above the upper support endpoint. -/
@[simp]
theorem cdf_arcsineMeasure_of_one_le {x : ℝ} (hx : 1 ≤ x) : cdf arcsineMeasure x = 1 := by
  rw [cdf_arcsineMeasure_eq, arcsin_of_one_le (one_le_sqrt.mpr hx)]
  field_simp

end TauCeti.Probability
