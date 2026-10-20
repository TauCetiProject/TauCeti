/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.BetaPrime.Basic
public import TauCeti.Probability.Distributions.Beta.Quantile
public import Mathlib.Topology.Instances.EReal.Lemmas
import TauCeti.Probability.Quantile.Map

/-!
# Quantiles of beta-prime laws

The beta-prime quantile is the odds transform of the corresponding Beta quantile.  This file
also records its one-sided limits at the support endpoints zero and infinity.

## Main results

* `TauCeti.Probability.quantile_betaPrimeMeasure` — the inverse-Beta quantile formula;
* `TauCeti.Probability.tendsto_quantile_betaPrimeMeasure_nhdsGT_zero` and
  `TauCeti.Probability.tendsto_quantile_betaPrimeMeasure_nhdsLT_one` — endpoint limits.

## References

* N. L. Johnson, S. Kotz, and N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), chapter 25.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {a b u : ℝ}

/-- The quantile of a beta-prime law is the odds transform of the inverse regularized incomplete
Beta function. -/
theorem quantile_betaPrimeMeasure (ha : 0 < a) (hb : 0 < b) (hu : u ∈ Ioo 0 1) :
    (betaPrimeMeasure a b).quantile u =
      inverseRegularizedIncompleteBeta a b u /
        (1 - inverseRegularizedIncompleteBeta a b u) := by
  rw [betaPrimeMeasure_eq_map ha hb]
  let _ : IsProbabilityMeasure (betaMeasure a b) := isProbabilityMeasureBeta ha hb
  rw [Measure.quantile_map_of_monotoneOn ordConnected_Ioo (ae_mem_Ioo_betaMeasure a b)
      ((fisherSnedecorMap_strictMonoOn (m := (2 : ℝ)) (n := 2) (by norm_num)
        (by norm_num)).monotoneOn.mono fun _ hx ↦ hx.2)
      (fun x hx ↦ by
        exact (hasDerivAt_fisherSnedecorMap (2 : ℝ) 2 hx.2.ne).continuousAt.continuousWithinAt)
      hu.1 hu.2,
    quantile_betaMeasure ha hb hu, fisherSnedecorMap_def]
  norm_num

/-- Beta-prime quantiles tend to zero as the probability level tends to zero from above. -/
theorem tendsto_quantile_betaPrimeMeasure_nhdsGT_zero (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun u ↦ ((betaPrimeMeasure a b).quantile u : EReal))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hmap : Tendsto (fisherSnedecorMap 2 2) (nhds 0) (nhds 0) := by
    have hfun : fisherSnedecorMap 2 2 = ((id : ℝ → ℝ) / fun u ↦ 1 - u) := by
      funext u
      rw [fisherSnedecorMap_def]
      norm_num
    rw [hfun]
    simpa only [Pi.div_apply, id_eq, zero_div] using
      tendsto_id.div (tendsto_const_nhds.sub tendsto_id)
        (by norm_num : (1 : ℝ) - 0 ≠ 0)
  have hlim := hmap.comp (tendsto_inverseRegularizedIncompleteBeta_zero ha hb)
  apply (EReal.tendsto_coe.mpr hlim).congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
  rw [Function.comp_apply, fisherSnedecorMap_def]
  norm_num
  exact (quantile_betaPrimeMeasure ha hb hu).symm

/-- Beta-prime quantiles tend to infinity as the probability level tends to one from below. -/
theorem tendsto_quantile_betaPrimeMeasure_nhdsLT_one (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun u ↦ ((betaPrimeMeasure a b).quantile u : EReal))
      (nhdsWithin 1 (Iio 1)) (nhds ⊤) := by
  have hsub : Tendsto (fun u : ℝ ↦ 1 - u) (nhdsWithin 1 (Iio 1))
      (nhdsWithin 0 (Ioi 0)) := by
    simpa only [Tendsto, Filter.map_subLeft_nhdsLT, sub_self] using
      (le_refl (nhdsWithin (0 : ℝ) (Ioi 0)))
  have hinv : Tendsto (fun u : ℝ ↦ (1 - u)⁻¹) (nhdsWithin 1 (Iio 1)) atTop :=
    tendsto_inv_nhdsGT_zero.comp hsub
  have hnum : Tendsto (id : ℝ → ℝ) (nhdsWithin 1 (Iio 1)) (nhds 1) :=
    (continuous_id.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  have hmap : Tendsto (fisherSnedecorMap 2 2) (nhdsWithin 1 (Iio 1)) atTop := by
    have hfun : fisherSnedecorMap 2 2 = fun u : ℝ ↦ (1 - u)⁻¹ * id u := by
      funext u
      rw [fisherSnedecorMap_def]
      simp only [id_eq]
      norm_num
      ring
    rw [hfun]
    exact hinv.atTop_mul_pos one_pos hnum
  have hbeta : Tendsto (inverseRegularizedIncompleteBeta a b)
      (nhdsWithin 1 (Iio 1)) (nhdsWithin 1 (Iio 1)) := by
    refine tendsto_nhdsWithin_iff.mpr
      ⟨tendsto_inverseRegularizedIncompleteBeta_one ha hb, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    exact (inverseRegularizedIncompleteBeta_mem_Ioo ha hb hu.1 hu.2).2
  apply EReal.tendsto_coe_nhds_top_iff.mpr
  apply (hmap.comp hbeta).congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  rw [Function.comp_apply, fisherSnedecorMap_def]
  norm_num
  exact (quantile_betaPrimeMeasure ha hb hu).symm

end TauCeti.Probability
