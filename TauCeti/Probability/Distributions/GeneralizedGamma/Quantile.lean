/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.GeneralizedGamma.Cdf
public import TauCeti.Probability.Distributions.Gamma.Quantile
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Generalized gamma quantiles

Interior quantiles are scaled powers of inverse regularized Gamma values. A negative
power uses the complementary probability level. The quantiles increase continuously
from zero to positive infinity for either sign of the power parameter.

## References

* E. W. Stacy, *A Generalization of the Gamma Distribution*, Annals of Mathematical
  Statistics 33 (1962), 1187–1192. We also allow negative power parameters.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology

namespace TauCeti.Probability

variable {a c s u : ℝ}

/-- The generalized gamma quantile uses the level `u` for positive powers and `1 - u`
for negative powers. The formula is asserted only for interior probability levels. -/
@[simp]
theorem quantile_generalizedGammaMeasure (ha : 0 < a) (hc : c ≠ 0) (hs : 0 < s)
    (hu : u ∈ Ioo 0 1) :
    (generalizedGammaMeasure a c s).quantile u =
      s * inverseRegularizedGamma a (if 0 < c then u else 1 - u) ^ c⁻¹ := by
  let _ := isProbabilityMeasure_generalizedGammaMeasure ha hc hs
  have hcomp : 1 - u ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hlevel : (if 0 < c then u else 1 - u) ∈ Ioo (0 : ℝ) 1 := by
    split_ifs <;> assumption
  have hpos := inverseRegularizedGamma_pos ha hlevel
  refine eq_of_forall_lt_iff fun x ↦ ?_
  rw [Measure.lt_quantile_iff _ hu.1 hu.2, cdf_generalizedGammaMeasure_eq ha hc hs]
  by_cases hx : x ≤ 0
  · simp only [ite_eq_left hx]
    exact iff_of_true hu.1 (hx.trans_lt (mul_pos hs (rpow_pos_of_pos hpos _)))
  · rw [ite_eq_right hx]
    split_ifs with hpow
    · rw [← lt_inverseRegularizedGamma_iff ha hu, mul_comm s, ← div_lt_iff₀ hs,
        lt_rpow_inv_iff_of_pos (div_pos (not_le.mp hx) hs).le
          (inverseRegularizedGamma_pos ha hu).le hpow]
    · have hneg : c < 0 := lt_of_le_of_ne (not_lt.mp hpow) hc
      rw [mul_comm s, ← div_lt_iff₀ hs,
        lt_rpow_inv_iff_of_neg (div_pos (not_le.mp hx) hs)
          (inverseRegularizedGamma_pos ha hcomp) hneg,
        inverseRegularizedGamma_lt_iff ha hcomp]
      constructor <;> intro h <;> linarith

/-- Generalized gamma quantiles are continuous at interior levels, for either sign of `c`. -/
theorem continuousOn_quantile_generalizedGammaMeasure
    (ha : 0 < a) (hc : c ≠ 0) (hs : 0 < s) :
    ContinuousOn (generalizedGammaMeasure a c s).quantile (Ioo 0 1) := by
  have hlevel : ContinuousOn (fun u : ℝ ↦ if 0 < c then u else 1 - u) (Ioo 0 1) := by
    split_ifs <;> fun_prop
  have hmem : MapsTo (fun u : ℝ ↦ if 0 < c then u else 1 - u) (Ioo 0 1) (Ioo 0 1) := by
    intro u hu
    split_ifs
    · exact hu
    · exact ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hinv := (continuousOn_inverseRegularizedGamma ha).comp hlevel hmem
  have hpow := hinv.rpow_const (p := c⁻¹) fun u hu ↦
    Or.inl (inverseRegularizedGamma_pos ha (hmem hu)).ne'
  exact ((continuousOn_const (c := s)).mul hpow).congr fun u hu ↦
    quantile_generalizedGammaMeasure ha hc hs hu

/-- Quantiles tend to the lower support endpoint zero as the level decreases to zero. -/
theorem tendsto_quantile_generalizedGammaMeasure_nhdsGT_zero
    (ha : 0 < a) (hc : c ≠ 0) (hs : 0 < s) :
    Tendsto (fun u ↦ ((generalizedGammaMeasure a c s).quantile u : EReal))
      (𝓝[>] 0) (𝓝 0) := by
  let _ := isProbabilityMeasure_generalizedGammaMeasure ha hc hs
  apply EReal.tendsto_coe.2
  refine tendsto_order.2 ⟨fun b hb ↦ ?_, fun b hb ↦ ?_⟩
  · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
    have hq : 0 < (generalizedGammaMeasure a c s).quantile u := by
      rw [Measure.lt_quantile_iff _ hu.1 hu.2, cdf_generalizedGammaMeasure_eq ha hc hs]
      simpa using hu.1
    exact hb.trans hq
  · have hbF := (cdf_generalizedGammaMeasure_pos_iff ha hc hs).2 (by linarith : 0 < b / 2)
    filter_upwards [Ioo_mem_nhdsGT hbF] with u hu
    exact lt_of_le_of_lt ((Measure.quantile_le_iff _ hu.1
      (hu.2.trans (cdf_generalizedGammaMeasure_lt_one ha hc hs (b / 2)))).2
        (hu.2.le)) (by linarith : b / 2 < b)

/-- Quantiles tend to positive infinity as the level increases to one. -/
theorem tendsto_quantile_generalizedGammaMeasure_nhdsLT_one
    (ha : 0 < a) (hc : c ≠ 0) (hs : 0 < s) :
    Tendsto (fun u ↦ ((generalizedGammaMeasure a c s).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ⊤) := by
  let _ := isProbabilityMeasure_generalizedGammaMeasure ha hc hs
  rw [EReal.tendsto_coe_nhds_top_iff]
  refine tendsto_atTop.2 fun b ↦ ?_
  filter_upwards [Ioo_mem_nhdsLT (cdf_generalizedGammaMeasure_lt_one ha hc hs b)] with u hu
  exact ((Measure.lt_quantile_iff _ ((cdf_nonneg _ b).trans_lt hu.1) hu.2).2 hu.1).le

end TauCeti.Probability
