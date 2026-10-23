/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.GeneralizedGamma.Basic
public import TauCeti.Probability.Distributions.Gamma.Cdf

/-!
# Generalized gamma cumulative distribution functions

The cdf of `s * G ^ c⁻¹`, for a unit-rate Gamma variable `G`, is the regularized
Gamma function at `(x / s) ^ c` when `c > 0`, and its complement when `c < 0`.
Both branches vanish on the nonpositive half-line. The sign change records the
reversal of order by a negative power and is needed to invert the cdf correctly.

## References

* E. W. Stacy, *A Generalization of the Gamma Distribution*, Annals of Mathematical
  Statistics 33 (1962), 1187–1192. We also allow negative power parameters.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

variable {a c s x : ℝ}

/-- The generalized gamma cdf is a lower or upper regularized Gamma value according
to the sign of the power parameter, and is zero at every nonpositive argument. -/
@[simp]
theorem cdf_generalizedGammaMeasure_eq (ha : 0 < a) (hc : c ≠ 0) (hs : 0 < s) (x : ℝ) :
    cdf (generalizedGammaMeasure a c s) x =
      if x ≤ 0 then 0 else
        if 0 < c then regularizedGamma a ((x / s) ^ c)
        else 1 - regularizedGamma a ((x / s) ^ c) := by
  let _ := isProbabilityMeasure_generalizedGammaMeasure ha hc hs
  let _ := isProbabilityMeasure_gammaMeasure ha zero_lt_one
  rw [cdf_eq_real]
  split_ifs with hx hpos
  · rw [measureReal_eq_zero_iff, measure_eq_zero_iff_ae_notMem]
    filter_upwards [ae_pos_generalizedGammaMeasure a c s] with y hy
    exact not_le.mpr (hx.trans_lt hy)
  · rw [generalizedGammaMeasure_of_valid ha hc hs,
      map_measureReal_apply (by fun_prop) measurableSet_Iic]
    have hpre : (fun y : ℝ ↦ s * y ^ c⁻¹) ⁻¹' Iic x =ᵐ[gammaMeasure a 1]
        Iic ((x / s) ^ c) := by
      filter_upwards [ae_pos_gammaMeasure a 1] with y hy
      simp only [mem_preimage, mem_Iic]
      rw [mul_comm s, ← le_div_iff₀ hs,
        rpow_inv_le_iff_of_pos hy.le (div_pos (not_le.mp hx) hs).le hpos]
    rw [measureReal_congr hpre, measureReal_Iic_gammaMeasure ha zero_lt_one, one_mul]
  · rw [generalizedGammaMeasure_of_valid ha hc hs,
      map_measureReal_apply (by fun_prop) measurableSet_Iic]
    have hpre : (fun y : ℝ ↦ s * y ^ c⁻¹) ⁻¹' Iic x =ᵐ[gammaMeasure a 1]
        Ioi ((x / s) ^ c) := by
      refine Filter.EventuallyEq.trans ?_ (Ioi_ae_eq_Ici' (measure_singleton _)).symm
      filter_upwards [ae_pos_gammaMeasure a 1] with y hy
      simp only [mem_preimage, mem_Iic, mem_Ici]
      rw [mul_comm s, ← le_div_iff₀ hs,
        rpow_inv_le_iff_of_neg hy (div_pos (not_le.mp hx) hs) (lt_of_le_of_ne (not_lt.mp hpos) hc)]
    rw [measureReal_congr hpre, measureReal_Ioi_gammaMeasure ha zero_lt_one, one_mul]

/-- Every finite point has positive survival under a valid generalized gamma law. -/
theorem cdf_generalizedGammaMeasure_lt_one (ha : 0 < a) (hc : c ≠ 0) (hs : 0 < s)
    (x : ℝ) : cdf (generalizedGammaMeasure a c s) x < 1 := by
  rw [cdf_generalizedGammaMeasure_eq ha hc hs]
  split_ifs with hx hpos
  · exact zero_lt_one
  · exact regularizedGamma_lt_one _ _
  · have := regularizedGamma_pos ha (rpow_pos_of_pos (div_pos (not_le.mp hx) hs) c)
    linarith

/-- The cdf is positive exactly on the positive half-line. -/
-- The CDF formula is the simp normal form; use this equivalence with `rw`.
theorem cdf_generalizedGammaMeasure_pos_iff (ha : 0 < a) (hc : c ≠ 0) (hs : 0 < s) :
    0 < cdf (generalizedGammaMeasure a c s) x ↔ 0 < x := by
  rw [cdf_generalizedGammaMeasure_eq ha hc hs]
  split_ifs with hx hpos
  · simp [not_lt.mpr hx]
  · exact iff_of_true (regularizedGamma_pos ha
      (rpow_pos_of_pos (div_pos (not_le.mp hx) hs) c)) (not_le.mp hx)
  · exact iff_of_true (sub_pos.mpr (regularizedGamma_lt_one _ _)) (not_le.mp hx)

end TauCeti.Probability
