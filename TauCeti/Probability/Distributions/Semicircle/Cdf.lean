/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Semicircle.PDF
import TauCeti.Probability.Cdf.Density
import TauCeti.Probability.Distributions.Beta.Cdf
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Cumulative distribution function of the semicircle law

On `[-1, 1]` the semicircle cdf is `1 / 2 + (x * √(1 - x²) + arcsin x) / π`.
Below and above this interval it is respectively zero and one. Its continuous density is
its derivative everywhere, even at the support endpoints.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, Chapter 25.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

/-- The semicircle cdf has derivative equal to the density at every real point. -/
theorem hasDerivAt_cdf_semicircleMeasure (x : ℝ) :
    HasDerivAt (cdf semicircleMeasure) (semicirclePDFReal x) x := by
  have hμ : semicircleMeasure =
      volume.withDensity (fun y ↦ ENNReal.ofReal (semicirclePDFReal y)) := by
    rw [← funext semicirclePDF_apply]
    exact semicircleMeasure_eq_withDensity
  exact hasDerivAt_cdf_of_eq_withDensity (f := semicirclePDFReal) hμ
    continuous_semicirclePDFReal.measurable.aemeasurable
    (.of_forall semicirclePDFReal_nonneg) continuous_semicirclePDFReal.continuousAt

/-- The semicircle cdf takes value one half at zero. -/
@[simp]
theorem cdf_semicircleMeasure_zero : cdf semicircleMeasure 0 = 1 / 2 := by
  let _ : IsProbabilityMeasure (betaMeasure (3 / 2) (3 / 2)) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  rw [semicircleMeasure_eq_map_betaMeasure, cdf_map_affine_of_pos (by norm_num),
    cdf_betaMeasure_eq (by norm_num) (by norm_num)]
  norm_num only
  have h := regularizedIncompleteBeta_symm
    (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num : (0 : ℝ) < 3 / 2) (1 / 2)
  norm_num only at h
  linarith

private lemma hasDerivAt_semicircle_cdf_formula {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y : ℝ ↦ 1 / 2 + (y * √(1 - y ^ 2) + arcsin y) / π)
      (semicirclePDFReal x) x := by
  have hpos : 0 < 1 - x ^ 2 := by
    nlinarith [mul_pos (by linarith [hx.1] : 0 < x + 1)
      (by linarith [hx.2] : 0 < 1 - x)]
  have hs := ((hasDerivAt_id x).pow 2).const_sub 1 |>.sqrt hpos.ne'
  convert (((hasDerivAt_id x).mul hs).add
    (hasDerivAt_arcsin hx.1.ne' hx.2.ne)).div_const π |>.const_add (1 / 2) using 1
  · rfl
  · simp only [id_eq, Pi.pow_apply, mul_one, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    rw [semicirclePDFReal_apply]
    have hsq := sq_sqrt hpos.le
    have hne := (sqrt_pos.2 hpos).ne'
    field_simp
    nlinarith

/-- The elementary semicircle cdf formula on the closed support interval. -/
theorem cdf_semicircleMeasure_of_mem_Icc {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    cdf semicircleMeasure x = 1 / 2 + (x * √(1 - x ^ 2) + arcsin x) / π := by
  have heq : EqOn (cdf semicircleMeasure)
      (fun y : ℝ ↦ 1 / 2 + (y * √(1 - y ^ 2) + arcsin y) / π) (Ioo (-1) 1) := by
    apply isOpen_Ioo.eqOn_of_deriv_eq (convex_Ioo (-1 : ℝ) 1).isPreconnected
      (fun y _ ↦ (hasDerivAt_cdf_semicircleMeasure y).differentiableAt.differentiableWithinAt)
      (fun y hy ↦ (hasDerivAt_semicircle_cdf_formula hy).differentiableAt.differentiableWithinAt)
      (fun y hy ↦ ?_) (x := 0) (by norm_num)
    · simp
    · rw [(hasDerivAt_cdf_semicircleMeasure y).deriv,
        (hasDerivAt_semicircle_cdf_formula hy).deriv]
  have hclosure := heq.closure (Measure.continuous_cdf_of_noAtoms _) (by fun_prop)
  rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)] at hclosure
  exact hclosure hx

/-- The semicircle cdf is zero at and below the lower support endpoint. -/
@[simp]
theorem cdf_semicircleMeasure_of_le_neg_one {x : ℝ} (hx : x ≤ -1) :
    cdf semicircleMeasure x = 0 := by
  apply le_antisymm _ (cdf_nonneg semicircleMeasure x)
  calc
    cdf semicircleMeasure x ≤ cdf semicircleMeasure (-1) := monotone_cdf _ hx
    _ = 0 := by
      rw [cdf_semicircleMeasure_of_mem_Icc (by norm_num)]
      norm_num
      field_simp
      ring

/-- The semicircle cdf is one at and above the upper support endpoint. -/
@[simp]
theorem cdf_semicircleMeasure_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    cdf semicircleMeasure x = 1 := by
  apply le_antisymm (cdf_le_one semicircleMeasure x)
  calc
    1 = cdf semicircleMeasure 1 := by
      rw [cdf_semicircleMeasure_of_mem_Icc (by norm_num)]
      norm_num
      field_simp
      ring
    _ ≤ cdf semicircleMeasure x := monotone_cdf _ hx

/-- The semicircle cdf, including the zero and one extensions beyond the support. -/
theorem cdf_semicircleMeasure_eq (x : ℝ) :
    cdf semicircleMeasure x = if x ≤ -1 then 0 else if 1 ≤ x then 1 else
      1 / 2 + (x * √(1 - x ^ 2) + arcsin x) / π := by
  split_ifs with hl hr
  · exact cdf_semicircleMeasure_of_le_neg_one hl
  · exact cdf_semicircleMeasure_of_one_le hr
  · exact cdf_semicircleMeasure_of_mem_Icc ⟨by linarith, by linarith⟩

end TauCeti.Probability
