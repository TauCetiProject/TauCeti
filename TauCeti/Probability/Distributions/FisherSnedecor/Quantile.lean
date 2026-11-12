/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Beta.Quantile
public import TauCeti.Probability.Distributions.FisherSnedecor.Basic
import TauCeti.Probability.Quantile.Map

/-!
# Quantiles of Fisher's F laws

For positive numerator and denominator degrees of freedom `m` and `n`, the Fisher--Snedecor
quantile is obtained by applying the beta-to-F transformation to the quantile of a
`Beta (m / 2, n / 2)` law. Thus, if

`b = inverseRegularizedIncompleteBeta (m / 2) (n / 2) u`,

then the quantile at an interior probability level `u` is `(n / m) * b / (1 - b)`. The
one-sided endpoint limits are `0` and `+∞`, matching the support of the law.

## Main results

* `TauCeti.Probability.quantile_fisherSnedecorMeasure` gives the explicit quantile formula.
* `TauCeti.Probability.tendsto_quantile_fisherSnedecorMeasure_nhdsGT_zero` and
  `TauCeti.Probability.tendsto_quantile_fisherSnedecorMeasure_nhdsLT_one` give the support-endpoint
  limits.

## References

* N. L. Johnson, S. Kotz, and N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), chapter 27.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {m n u : ℝ}

/-- The quantile of a Fisher--Snedecor law with positive degrees of freedom is the beta-to-F
transform of the corresponding Beta quantile. -/
theorem quantile_fisherSnedecorMeasure (hm : 0 < m) (hn : 0 < n) (hu : u ∈ Ioo 0 1) :
    (fisherSnedecorMeasure m n).quantile u =
      (n / m) * inverseRegularizedIncompleteBeta (m / 2) (n / 2) u /
        (1 - inverseRegularizedIncompleteBeta (m / 2) (n / 2) u) := by
  rw [fisherSnedecorMeasure_eq_map hm hn]
  let _ : IsProbabilityMeasure (betaMeasure (m / 2) (n / 2)) :=
    isProbabilityMeasureBeta (by linarith) (by linarith)
  rw [Measure.quantile_map_of_monotoneOn ordConnected_Ioo
      (ae_mem_Ioo_betaMeasure (m / 2) (n / 2))
      ((fisherSnedecorMap_strictMonoOn hm hn).monotoneOn.mono fun _ hx ↦ hx.2)
      (fun x hx ↦
        (hasDerivAt_fisherSnedecorMap m n (ne_of_lt hx.2)).continuousAt.continuousWithinAt)
      hu.1 hu.2,
    quantile_betaMeasure (by linarith) (by linarith) hu, fisherSnedecorMap_def]

/-- Fisher--Snedecor quantiles tend to the lower support endpoint `0` as the probability level
tends to zero from above. -/
theorem tendsto_quantile_fisherSnedecorMeasure_nhdsGT_zero (hm : 0 < m) (hn : 0 < n) :
    Tendsto (fun u ↦ (fisherSnedecorMeasure m n).quantile u) (𝓝[>] 0) (𝓝 0) := by
  have hlim : Tendsto
      (fun u ↦ fisherSnedecorMap m n
        (inverseRegularizedIncompleteBeta (m / 2) (n / 2) u))
      (𝓝[>] 0) (𝓝 0) := by
    have hcont := (hasDerivAt_fisherSnedecorMap m n
      (u := 0) (by norm_num)).continuousAt.tendsto
    have hcomp := hcont.comp
      (tendsto_inverseRegularizedIncompleteBeta_zero
        (by linarith : 0 < m / 2) (by linarith : 0 < n / 2))
    have hzero : fisherSnedecorMap m n 0 = 0 := by
      rw [fisherSnedecorMap_def]
      norm_num
    rw [hzero] at hcomp
    exact hcomp
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
  rw [fisherSnedecorMap_def]
  exact (quantile_fisherSnedecorMeasure hm hn hu).symm

/-- Fisher--Snedecor quantiles tend to infinity as the probability level tends to one from
below. -/
theorem tendsto_quantile_fisherSnedecorMeasure_nhdsLT_one (hm : 0 < m) (hn : 0 < n) :
    Tendsto (fun u ↦ (fisherSnedecorMeasure m n).quantile u) (𝓝[<] 1) atTop := by
  have hbeta := tendsto_inverseRegularizedIncompleteBeta_one
    (by linarith : 0 < m / 2) (by linarith : 0 < n / 2)
  have hden : Tendsto
      (fun u ↦ 1 - inverseRegularizedIncompleteBeta (m / 2) (n / 2) u)
      (𝓝[<] 1) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hsub : Tendsto
          (fun u ↦ (1 : ℝ) - inverseRegularizedIncompleteBeta (m / 2) (n / 2) u)
          (𝓝[<] 1) (𝓝 (1 - 1)) := tendsto_const_nhds.sub hbeta
      simpa using hsub
    · filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
      exact sub_pos.mpr
        (inverseRegularizedIncompleteBeta_mem_Ioo
          (by linarith) (by linarith) hu.1 hu.2).2
  have hnum : Tendsto
      (fun u ↦ (n / m) * inverseRegularizedIncompleteBeta (m / 2) (n / 2) u)
      (𝓝[<] 1) (𝓝 (n / m)) := by
    simpa using tendsto_const_nhds.mul hbeta
  have hlim : Tendsto
      (fun u ↦ (n / m) * inverseRegularizedIncompleteBeta (m / 2) (n / 2) u /
        (1 - inverseRegularizedIncompleteBeta (m / 2) (n / 2) u))
      (𝓝[<] 1) atTop := by
    simpa [div_eq_mul_inv] using
      hnum.pos_mul_atTop (div_pos hn hm) (tendsto_inv_nhdsGT_zero.comp hden)
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  exact (quantile_fisherSnedecorMeasure hm hn hu).symm

end TauCeti.Probability
