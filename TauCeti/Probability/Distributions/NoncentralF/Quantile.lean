/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NoncentralF.Cdf
public import TauCeti.Probability.Quantile

/-!
# Quantiles of noncentral F laws

For positive degrees of freedom, the quantile at an interior probability level is the
unique positive root of the Poisson-series cdf. Quantiles are continuous and strictly
increasing in the level, with one-sided limits zero and positive infinity. This gives
an inverse characterization without introducing another inverse special function.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 30.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Topology
open scoped NNReal

namespace TauCeti.Probability

variable {m n u x : ℝ} {l : ℝ≥0}

/-- Every interior noncentral F quantile is strictly positive. -/
theorem quantile_noncentralFMeasure_pos (hm : 0 < m) (hn : 0 < n) (l : ℝ≥0)
    (hu : u ∈ Ioo 0 1) : 0 < (noncentralFMeasure m n l).quantile u := by
  let _ := isProbabilityMeasure_noncentralFMeasure hm hn l
  exact ordConnected_Ioi.quantile_mem (ae_pos_noncentralFMeasure m n l) hu.1 hu.2

/-- An interior noncentral F quantile is the unique positive root of the explicit
Poisson series of incomplete Beta functions. -/
theorem quantile_noncentralFMeasure_eq_iff (hm : 0 < m) (hn : 0 < n) (l : ℝ≥0)
    (hu : u ∈ Ioo 0 1) :
    (noncentralFMeasure m n l).quantile u = x ↔ 0 < x ∧
      (∑' j : ℕ, (exp (-(l : ℝ) / 2) * ((l : ℝ) / 2) ^ j / j.factorial) *
        regularizedIncompleteBeta ((m + 2 * j) / 2) (n / 2) (m * x / (n + m * x))) = u := by
  have hpos := quantile_noncentralFMeasure_pos hm hn l hu
  have hroot := Measure.cdf_quantile _ (continuous_cdf_noncentralFMeasure hm hn l) hu.1 hu.2
  constructor
  · rintro rfl
    refine ⟨hpos, ?_⟩
    rwa [cdf_noncentralFMeasure_eq hm hn l, ite_eq_right hpos.not_ge] at hroot
  · rintro ⟨hx, hsum⟩
    apply (strictMonoOn_cdf_noncentralFMeasure hm hn l).injOn hpos.le hx.le
    rw [hroot, cdf_noncentralFMeasure_eq hm hn l, ite_eq_right hx.not_ge, hsum]

/-- Noncentral F quantiles increase strictly at interior probability levels. -/
theorem strictMonoOn_quantile_noncentralFMeasure (hm : 0 < m) (hn : 0 < n) (l : ℝ≥0) :
    StrictMonoOn (noncentralFMeasure m n l).quantile (Ioo 0 1) :=
  Measure.strictMonoOn_quantile _ (continuous_cdf_noncentralFMeasure hm hn l)

/-- The noncentral F quantile is continuous at every interior probability level. -/
theorem continuousOn_quantile_noncentralFMeasure (hm : 0 < m) (hn : 0 < n) (l : ℝ≥0) :
    ContinuousOn (noncentralFMeasure m n l).quantile (Ioo 0 1) :=
  Measure.continuousOn_quantile_of_strictMonoOn _ ordConnected_Ioi
    ((strictMonoOn_cdf_noncentralFMeasure hm hn l).mono Ioi_subset_Ici_self)
    (fun _ hu ↦ quantile_noncentralFMeasure_pos hm hn l hu)

/-- As the probability level decreases to zero, the noncentral F quantile tends to zero. -/
theorem tendsto_quantile_noncentralFMeasure_nhdsGT_zero (hm : 0 < m) (hn : 0 < n) (l : ℝ≥0) :
    Filter.Tendsto (fun u ↦ ((noncentralFMeasure m n l).quantile u : EReal))
      (𝓝[>] 0) (𝓝 0) := by
  let _ := isProbabilityMeasure_noncentralFMeasure hm hn l
  exact Measure.tendsto_quantile_nhdsGT_zero_of_ae_le_of_cdf_pos _
    ((ae_pos_noncentralFMeasure m n l).mono fun _ hx ↦ hx.le)
    (fun _ hx ↦ (cdf_noncentralFMeasure_pos_iff hm hn l).2 hx)

/-- As the probability level increases to one, the noncentral F quantile tends to infinity. -/
theorem tendsto_quantile_noncentralFMeasure_nhdsLT_one (hm : 0 < m) (hn : 0 < n) (l : ℝ≥0) :
    Filter.Tendsto (fun u ↦ ((noncentralFMeasure m n l).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ⊤) :=
  Measure.tendsto_quantile_nhdsLT_one_of_cdf_lt_one _ (cdf_noncentralFMeasure_lt_one hm hn l)

end TauCeti.Probability
