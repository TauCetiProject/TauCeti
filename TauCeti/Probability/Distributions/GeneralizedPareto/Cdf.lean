/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.GeneralizedPareto.Basic
import TauCeti.Probability.Cdf

/-!
# Cumulative distribution functions of generalized Pareto laws

For positive scale `s` and nonzero shape `ξ`, the generalized Pareto cdf is
`1 - (1 + ξ * x / s) ^ (-1 / ξ)` on the nonnegative part of its support interior.
It is zero at and below zero, and one at and above the finite upper endpoint `-s / ξ`
when `ξ < 0`. At zero shape it is the exponential cdf.

The proofs use the increasing exponential-variable transformation. Its cdf identity at a
transformed point also gives a direct way to compute probabilities without choosing a shape
branch.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  Chapter 4.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

variable {s ξ x : ℝ}

/-- The cdf at a transformed point is the cdf of the source exponential variable. -/
theorem cdf_generalizedParetoMeasure_generalizedParetoMap (hs : 0 < s) (ξ e : ℝ) :
    cdf (generalizedParetoMeasure s ξ) (generalizedParetoMap s ξ e) =
      cdf (expMeasure 1) e := by
  let _ := isProbabilityMeasure_expMeasure one_pos
  let _ := isProbabilityMeasure_generalizedParetoMeasure hs ξ
  rw [cdf_eq_real, generalizedParetoMeasure_of_pos hs,
    map_measureReal_apply (measurable_generalizedParetoMap_right s ξ) measurableSet_Iic,
    cdf_eq_real]
  congr 1
  ext y
  exact (strictMono_generalizedParetoMap hs ξ).le_iff_le

/-- The generalized Pareto cdf vanishes at and below zero. -/
theorem cdf_generalizedParetoMeasure_of_nonpos (hs : 0 < s) (ξ : ℝ) (hx : x ≤ 0) :
    cdf (generalizedParetoMeasure s ξ) x = 0 := by
  have hcdf := cdf_generalizedParetoMeasure_generalizedParetoMap hs ξ 0
  rw [generalizedParetoMap_apply_zero, cdf_expMeasure_eq one_pos] at hcdf
  simp only [le_refl, ite_true, mul_zero, neg_zero, Real.exp_zero, sub_self] at hcdf
  exact le_antisymm (hcdf ▸ monotone_cdf _ hx) (cdf_nonneg _ _)

/-- At nonzero shape the generalized Pareto cdf has its usual power formula wherever
`x ≥ 0` and `1 + ξ * x / s > 0`. -/
theorem cdf_generalizedParetoMeasure_of_shape_ne_zero (hs : 0 < s) (hξ : ξ ≠ 0)
    (hx : 0 ≤ x) (hw : 0 < 1 + ξ * x / s) :
    cdf (generalizedParetoMeasure s ξ) x = 1 - (1 + ξ * x / s) ^ (-1 / ξ) := by
  have hinv := generalizedParetoMap_log_div hs.ne' hξ hw
  have he : 0 ≤ Real.log (1 + ξ * x / s) / ξ := by
    rwa [← generalizedParetoMap_nonneg_iff hs ξ, hinv]
  rw [← hinv, cdf_generalizedParetoMeasure_generalizedParetoMap hs, cdf_expMeasure_eq one_pos,
    ite_eq_left he, hinv, one_mul, Real.rpow_def_of_pos hw]
  congr 2
  ring

/-- For negative shape the cdf is one at and beyond the finite upper endpoint. -/
theorem cdf_generalizedParetoMeasure_eq_one_of_neg_div_le (hs : 0 < s) (hξ : ξ < 0)
    (hx : -s / ξ ≤ x) : cdf (generalizedParetoMeasure s ξ) x = 1 := by
  let _ := isProbabilityMeasure_expMeasure one_pos
  let _ := isProbabilityMeasure_generalizedParetoMeasure hs ξ
  have hpre : (generalizedParetoMap s ξ) ⁻¹' Iic x = univ := by
    apply eq_univ_of_forall
    intro e
    apply le_trans _ hx
    rw [generalizedParetoMap_of_shape_ne_zero hξ.ne, div_le_div_right_of_neg hξ]
    nlinarith [mul_pos hs (Real.exp_pos (ξ * e))]
  rw [cdf_eq_real, generalizedParetoMeasure_of_pos hs,
    map_measureReal_apply (measurable_generalizedParetoMap_right s ξ) measurableSet_Iic,
    hpre]
  simp

/-- The full generalized Pareto cdf, with its lower, zero-shape, and finite-upper-endpoint
branches explicit. -/
theorem cdf_generalizedParetoMeasure_eq (hs : 0 < s) (ξ x : ℝ) :
    cdf (generalizedParetoMeasure s ξ) x =
      if x ≤ 0 then 0 else if ξ = 0 then 1 - Real.exp (-x / s)
      else if 0 < 1 + ξ * x / s then 1 - (1 + ξ * x / s) ^ (-1 / ξ) else 1 := by
  split_ifs with hx hξ hw
  · exact cdf_generalizedParetoMeasure_of_nonpos hs ξ hx
  · rw [hξ, generalizedParetoMeasure_zero hs, cdf_expMeasure_eq (inv_pos.mpr hs),
      ite_eq_left (le_of_not_ge hx)]
    congr 2
    ring
  · exact cdf_generalizedParetoMeasure_of_shape_ne_zero hs hξ (le_of_not_ge hx) hw
  · have hξneg : ξ < 0 := by
      by_contra h
      have := div_nonneg (mul_nonneg (le_of_not_gt h) (le_of_not_ge hx)) hs.le
      linarith
    apply cdf_generalizedParetoMeasure_eq_one_of_neg_div_le hs hξneg
    apply (div_le_iff_of_neg hξneg).2
    have := (div_le_iff₀ hs).1 (show ξ * x / s ≤ -1 by linarith)
    nlinarith

/-- On the nonnegative half-line, generalized Pareto survival is positive exactly below
the upper endpoint, when there is one. -/
@[simp]
theorem cdf_generalizedParetoMeasure_lt_one_iff (hs : 0 < s) (hx : 0 ≤ x) :
    cdf (generalizedParetoMeasure s ξ) x < 1 ↔ 0 < s + ξ * x := by
  have hb : 0 < 1 + ξ * x / s ↔ 0 < s + ξ * x := by
    have h : 1 + ξ * x / s = (s + ξ * x) / s := by field_simp
    rw [h]
    exact div_pos_iff_of_pos_right hs
  rcases hx.eq_or_lt with rfl | hx
  · simp [cdf_generalizedParetoMeasure_of_nonpos hs ξ le_rfl, hs]
  by_cases hξ : ξ = 0
  · subst ξ
    simp [generalizedParetoMeasure_zero hs, cdf_expMeasure_eq (inv_pos.mpr hs),
      hx.le, Real.exp_pos, hs]
  rw [cdf_generalizedParetoMeasure_eq hs]
  simp only [hx.not_ge, hξ, ↓reduceIte]
  split_ifs with h
  · exact iff_of_true (by linarith [Real.rpow_pos_of_pos h (-1 / ξ)]) (hb.1 h)
  · simp [not_lt.mp (mt hb.2 h)]

/-- The generalized Pareto cdf is continuous at every real point, including both support
endpoints. -/
theorem continuous_cdf_generalizedParetoMeasure (hs : 0 < s) (ξ : ℝ) :
    Continuous (cdf (generalizedParetoMeasure s ξ)) := by
  let _ := isProbabilityMeasure_generalizedParetoMeasure hs ξ
  let _ := nullSingletonClass_generalizedParetoMeasure hs ξ
  exact Measure.continuous_cdf_of_noAtoms _

end TauCeti.Probability
