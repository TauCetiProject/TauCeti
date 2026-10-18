/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Beta.Quantile
public import TauCeti.Probability.Distributions.FisherSnedecor.Cdf
public import TauCeti.Probability.Quantile.Map

/-!
# Quantiles of the Fisher--Snedecor distribution

This file evaluates the quantile function of the Fisher--Snedecor distribution in terms of the
inverse regularized incomplete beta function. It also records the limiting values at both ends of
the probability interval.

## Main results

* `quantile_fisherSnedecorMeasure` gives the quantile for probabilities strictly between zero and
  one.
* `tendsto_quantile_fisherSnedecorMeasure_nhdsGT_zero` and
  `tendsto_quantile_fisherSnedecorMeasure_nhdsLT_one` give the one-sided endpoint limits.

## References

* N. L. Johnson, S. Kotz, and N. Balakrishnan, *Continuous Univariate Distributions, Volume 2*,
  Chapter 27
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {m n u : ℝ}

/-- The quantile of the Fisher--Snedecor distribution is obtained by applying its beta-to-Fisher
transformation to the corresponding beta quantile. -/
@[simp]
theorem quantile_fisherSnedecorMeasure (hm : 0 < m) (hn : 0 < n) (hu : u ∈ Ioo 0 1) :
    (fisherSnedecorMeasure m n).quantile u =
      (n / m) * inverseRegularizedIncompleteBeta (m / 2) (n / 2) u /
        (1 - inverseRegularizedIncompleteBeta (m / 2) (n / 2) u) := by
  have hm2 : 0 < m / 2 := by positivity
  have hn2 : 0 < n / 2 := by positivity
  let _ := isProbabilityMeasureBeta hm2 hn2
  have hmem : ∀ᵐ x ∂betaMeasure (m / 2) (n / 2), x ∈ Iio (1 : ℝ) :=
    (ae_mem_Ioo_betaMeasure (m / 2) (n / 2)).mono fun _ hx => hx.2
  have hcont : ContinuousOn (fisherSnedecorMap m n) (Iio 1) := fun x hx =>
    (hasDerivAt_fisherSnedecorMap m n (ne_of_lt hx)).continuousAt.continuousWithinAt
  rw [fisherSnedecorMeasure_eq_map hm hn]
  rw [Measure.quantile_map_of_monotoneOn ordConnected_Iio hmem
    (fisherSnedecorMap_strictMonoOn hm hn).monotoneOn hcont hu.1 hu.2]
  rw [quantile_betaMeasure hm2 hn2 hu]
  rw [fisherSnedecorMap_def]

/-- The Fisher--Snedecor quantile tends to its lower support endpoint as the probability tends to
zero from above. -/
theorem tendsto_quantile_fisherSnedecorMeasure_nhdsGT_zero (hm : 0 < m) (hn : 0 < n) :
    Tendsto (fun u => (fisherSnedecorMeasure m n).quantile u) (𝓝[>] 0) (𝓝 0) := by
  have hm2 : 0 < m / 2 := by positivity
  have hn2 : 0 < n / 2 := by positivity
  have hlim : Tendsto
      (fun u => fisherSnedecorMap m n
        (inverseRegularizedIncompleteBeta (m / 2) (n / 2) u))
      (𝓝[>] 0) (𝓝 0) := by
    have hcont := (hasDerivAt_fisherSnedecorMap m n (u := 0) (by norm_num)).continuousAt.tendsto
    have hcomp := hcont.comp (tendsto_inverseRegularizedIncompleteBeta_zero hm2 hn2)
    have hzero : fisherSnedecorMap m n 0 = 0 := by
      rw [fisherSnedecorMap_def]
      norm_num
    rw [hzero] at hcomp
    exact hcomp
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
  rw [fisherSnedecorMap_def]
  exact (quantile_fisherSnedecorMeasure hm hn hu).symm

/-- The Fisher--Snedecor quantile tends to infinity as the probability tends to one from below. -/
theorem tendsto_quantile_fisherSnedecorMeasure_nhdsLT_one (hm : 0 < m) (hn : 0 < n) :
    Tendsto (fun u => (fisherSnedecorMeasure m n).quantile u) (𝓝[<] 1) atTop := by
  have hm2 : 0 < m / 2 := by positivity
  have hn2 : 0 < n / 2 := by positivity
  have hbeta := tendsto_inverseRegularizedIncompleteBeta_one hm2 hn2
  have hden : Tendsto
      (fun u => 1 - inverseRegularizedIncompleteBeta (m / 2) (n / 2) u)
      (𝓝[<] 1) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hsub : Tendsto
          (fun u => (1 : ℝ) - inverseRegularizedIncompleteBeta (m / 2) (n / 2) u)
          (𝓝[<] 1) (𝓝 (1 - 1)) := tendsto_const_nhds.sub hbeta
      simpa using hsub
    · filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
      exact sub_pos.mpr
        (inverseRegularizedIncompleteBeta_mem_Ioo hm2 hn2 hu.1 hu.2).2
  have hnum : Tendsto
      (fun u => (n / m) * inverseRegularizedIncompleteBeta (m / 2) (n / 2) u)
      (𝓝[<] 1) (𝓝 (n / m)) := by
    simpa using tendsto_const_nhds.mul hbeta
  have hlim : Tendsto
      (fun u => (n / m) * inverseRegularizedIncompleteBeta (m / 2) (n / 2) u /
        (1 - inverseRegularizedIncompleteBeta (m / 2) (n / 2) u))
      (𝓝[<] 1) atTop := by
    simpa [div_eq_mul_inv] using
      hnum.pos_mul_atTop (div_pos hn hm) (tendsto_inv_nhdsGT_zero.comp hden)
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  exact (quantile_fisherSnedecorMeasure hm hn hu).symm

end TauCeti.Probability
