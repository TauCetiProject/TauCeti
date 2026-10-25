/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Kumaraswamy.Basic
public import TauCeti.Probability.Quantile

/-!
# Quantiles of the Kumaraswamy distribution

The Kumaraswamy cdf `1 - (1 - x ^ a) ^ b` on the unit interval inverts in closed form, which is
the main computational advantage of the law over the Beta law. This file proves that at an
interior probability level `u` the lower quantile is `(1 - (1 - u) ^ b⁻¹) ^ a⁻¹`. Consequently
its one-sided endpoint limits are the endpoints `0` and `1` of the support.

## Main results

* `TauCeti.Probability.quantile_kumaraswamyMeasure` gives the explicit quantile formula;
* `TauCeti.Probability.tendsto_quantile_kumaraswamyMeasure_nhdsGT_zero` and
  `TauCeti.Probability.tendsto_quantile_kumaraswamyMeasure_nhdsLT_one` give its endpoint limits.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology

namespace TauCeti.Probability

variable {a b u : ℝ}

/-- The lower quantile of a Kumaraswamy law with positive shape parameters. -/
theorem quantile_kumaraswamyMeasure (ha : 0 < a) (hb : 0 < b) (hu : u ∈ Ioo 0 1) :
    (kumaraswamyMeasure a b).quantile u = (1 - (1 - u) ^ b⁻¹) ^ a⁻¹ := by
  have hd0 : 0 < (1 - u) ^ b⁻¹ := rpow_pos_of_pos (sub_pos.mpr hu.2) _
  have hd1 : (1 - u) ^ b⁻¹ < 1 :=
    rpow_lt_one (sub_nonneg.mpr hu.2.le) (by linarith [hu.1]) (inv_pos.mpr hb)
  have hc0 : 0 < 1 - (1 - u) ^ b⁻¹ := sub_pos.mpr hd1
  have hq0 : 0 < (1 - (1 - u) ^ b⁻¹) ^ a⁻¹ := rpow_pos_of_pos hc0 _
  have hq1 : (1 - (1 - u) ^ b⁻¹) ^ a⁻¹ < 1 :=
    rpow_lt_one hc0.le (by linarith) (inv_pos.mpr ha)
  refine eq_of_forall_ge_iff fun x ↦ ?_
  rw [Measure.quantile_le_iff _ hu.1 hu.2]
  rcases le_or_gt x 0 with hx | hx
  · rw [cdf_kumaraswamyMeasure_of_nonpos ha hb hx]
    exact iff_of_false (not_le.mpr hu.1) (not_le.mpr (hx.trans_lt hq0))
  rcases le_or_gt 1 x with hx₁ | hx₁
  · rw [cdf_kumaraswamyMeasure_of_one_le ha hb hx₁]
    exact iff_of_true hu.2.le (hq1.le.trans hx₁)
  have hxa : x ^ a ≤ 1 := rpow_le_one hx.le hx₁.le ha.le
  rw [cdf_kumaraswamyMeasure_of_mem_Icc ha hb ⟨hx.le, hx₁.le⟩, le_sub_comm,
    ← le_rpow_inv_iff_of_pos (sub_nonneg.mpr hxa) (sub_nonneg.mpr hu.2.le) hb, sub_le_comm,
    rpow_inv_le_iff_of_pos hc0.le hx.le ha]

/-- The closed-form Kumaraswamy quantile is continuous in the level. -/
private theorem continuous_kumaraswamyQuantile (ha : 0 < a) (hb : 0 < b) :
    Continuous fun u : ℝ ↦ (1 - (1 - u) ^ b⁻¹) ^ a⁻¹ :=
  (continuous_const.sub ((continuous_const.sub continuous_id).rpow_const
    fun _ ↦ Or.inr (inv_nonneg.mpr hb.le))).rpow_const fun _ ↦ Or.inr (inv_nonneg.mpr ha.le)

/-- Kumaraswamy quantiles tend to the lower support endpoint `0` as the probability level tends
to zero from above. -/
theorem tendsto_quantile_kumaraswamyMeasure_nhdsGT_zero (ha : 0 < a) (hb : 0 < b) :
    Tendsto (kumaraswamyMeasure a b).quantile (𝓝[>] 0) (𝓝 0) := by
  have hlim := ((continuous_kumaraswamyQuantile ha hb).tendsto 0).mono_left
    (nhdsWithin_le_nhds (s := Ioi 0))
  rw [sub_zero, one_rpow, sub_self, zero_rpow (inv_ne_zero ha.ne')] at hlim
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT one_pos] with u hu
  exact (quantile_kumaraswamyMeasure ha hb hu).symm

/-- Kumaraswamy quantiles tend to the upper support endpoint `1` as the probability level tends
to one from below. -/
theorem tendsto_quantile_kumaraswamyMeasure_nhdsLT_one (ha : 0 < a) (hb : 0 < b) :
    Tendsto (kumaraswamyMeasure a b).quantile (𝓝[<] 1) (𝓝 1) := by
  have hlim := ((continuous_kumaraswamyQuantile ha hb).tendsto 1).mono_left
    (nhdsWithin_le_nhds (s := Iio 1))
  rw [sub_self, zero_rpow (inv_ne_zero hb.ne'), sub_zero, one_rpow] at hlim
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  exact (quantile_kumaraswamyMeasure ha hb hu).symm

end TauCeti.Probability
