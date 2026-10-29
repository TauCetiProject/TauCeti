/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.GeneralizedNormal.Gamma
public import TauCeti.Probability.Distributions.GeneralizedGamma.Cdf
public import Mathlib.Basic.Real.Sign
import TauCeti.Probability.Cdf.Density

/-!
# Generalized normal cumulative distribution functions

The generalized normal cdf is
`(1 + sign (x - m) * regularizedGamma p⁻¹ (|(x - m) / s| ^ p)) / 2`
at positive scale and shape. The cdf is continuous and strictly increasing on the
whole real line, and the law has full topological support. These facts allow its
quantile to be obtained by inverting the regularized Gamma function separately
on either side of the median `m`.

The cdf computation uses the symmetrization of a generalized gamma magnitude in
`generalizedNormalMeasure_eq_add_map_neg`.

## References

* S. Nadarajah, *A generalized normal distribution*, Journal of Applied Statistics
  32(7), 685–694 (2005).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace TauCeti.Probability

variable {m s p : ℝ}

private theorem cdf_generalizedNormalMeasure_centered (hs : 0 < s) (hp : 0 < p) (x : ℝ) :
    cdf (generalizedNormalMeasure 0 s p) x =
      (cdf (generalizedGammaMeasure p⁻¹ p s) x +
        (1 - cdf (generalizedGammaMeasure p⁻¹ p s) (-x))) / 2 := by
  let _ := isProbabilityMeasure_generalizedNormalMeasure hs hp 0
  let _ := isProbabilityMeasure_generalizedGammaMeasure (inv_pos.mpr hp) hp.ne' hs
  have hpre : (fun y : ℝ ↦ -y) ⁻¹' Iic x = Ici (-x) := by
    ext y
    simp only [mem_preimage, mem_Iic, mem_Ici, neg_le]
  have hneg : ((generalizedGammaMeasure p⁻¹ p s).map (fun y : ℝ ↦ -y)).real (Iic x) =
      1 - cdf (generalizedGammaMeasure p⁻¹ p s) (-x) := by
    rw [map_measureReal_apply measurable_neg measurableSet_Iic, hpre,
      ← compl_Iio, measureReal_compl measurableSet_Iio, probReal_univ,
      measureReal_congr Iio_ae_eq_Iic, ← cdf_eq_real]
  rw [cdf_eq_real, generalizedNormalMeasure_eq_add_map_neg,
    measureReal_add_apply (by simp only [Measure.smul_apply, smul_eq_mul]; finiteness)
      (by simp only [Measure.smul_apply, smul_eq_mul]; finiteness),
    measureReal_ennreal_smul_apply, measureReal_ennreal_smul_apply, hneg, ← cdf_eq_real]
  simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  ring

/-- The generalized normal cdf in terms of the regularized lower incomplete Gamma
function. The sign factor gives both tails and the value `1 / 2` at the location. -/
@[simp]
theorem cdf_generalizedNormalMeasure_eq (hs : 0 < s) (hp : 0 < p) (x : ℝ) :
    cdf (generalizedNormalMeasure m s p) x =
      (1 + sign (x - m) * regularizedGamma p⁻¹ (|(x - m) / s| ^ p)) / 2 := by
  have htranslate := generalizedNormalMeasure_map_affine 0 s p m (c := 1) one_ne_zero
  simp only [mul_zero, add_zero, abs_one, one_mul] at htranslate
  let _ := isProbabilityMeasure_generalizedNormalMeasure hs hp 0
  have hcdf := cdf_map_affine_of_pos (μ := generalizedNormalMeasure 0 s p) (a := m) one_pos x
  simp only [one_mul, div_one] at hcdf
  rw [← htranslate, hcdf,
    cdf_generalizedNormalMeasure_centered hs hp,
    cdf_generalizedGammaMeasure_eq (inv_pos.mpr hp) hp.ne' hs,
    cdf_generalizedGammaMeasure_eq (inv_pos.mpr hp) hp.ne' hs]
  rcases lt_trichotomy (x - m) 0 with hx | hx | hx
  · simp only [ite_eq_left hx.le, ite_eq_right (by linarith : ¬ (-(x - m) ≤ 0)),
      ite_eq_left hp, sign_of_neg hx, abs_of_neg (div_neg_of_neg_of_pos hx hs), neg_div]
    ring
  · simp [hx]
  · simp only [ite_eq_right (not_le.mpr hx), ite_eq_left (by linarith : -(x - m) ≤ 0),
      ite_eq_left hp, sign_of_pos hx, abs_of_pos (div_pos hx hs)]
    ring

/-- The cdf of a valid generalized normal law is strictly increasing everywhere. -/
theorem strictMono_cdf_generalizedNormalMeasure (hs : 0 < s) (hp : 0 < p) :
    StrictMono (cdf (generalizedNormalMeasure m s p)) := by
  let _ := isProbabilityMeasure_generalizedNormalMeasure hs hp m
  exact strictMono_cdf_of_eq_withDensity
    (by rw [generalizedNormalMeasure_eq_withDensity,
      funext (generalizedNormalPDF_eq_ofReal m s p)])
    (measurable_generalizedNormalPDFReal m s p).aemeasurable
    (generalizedNormalPDFReal_pos hs hp m)

/-- The cdf of a valid generalized normal law is continuous on the whole real line. -/
theorem continuous_cdf_generalizedNormalMeasure (hs : 0 < s) (hp : 0 < p) :
    Continuous (cdf (generalizedNormalMeasure m s p)) := by
  let _ := isProbabilityMeasure_generalizedNormalMeasure hs hp m
  exact Measure.continuous_cdf_of_noAtoms _

/-- A generalized normal law has full topological support at valid parameters and
empty support at invalid parameters. -/
@[simp]
theorem support_generalizedNormalMeasure (m s p : ℝ) :
    (generalizedNormalMeasure m s p).support = if 0 < s ∧ 0 < p then univ else ∅ := by
  split_ifs with h
  · let _ := isProbabilityMeasure_generalizedNormalMeasure h.1 h.2 m
    exact Measure.support_eq_univ_of_strictMono_cdf _
      (strictMono_cdf_generalizedNormalMeasure h.1 h.2)
  · rw [generalizedNormalMeasure_of_not_pos h, Measure.support_zero]

end TauCeti.Probability
