/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Logistic.Basic

/-!
# Logistic quantile regularity

The quantiles of a logistic law vary continuously and strictly increasingly on the interior
probability levels. As the level tends to zero or one, they tend respectively to minus or plus
infinity, matching the full support of the law.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley (1995), chapter 23.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {m s : ℝ}

/-- Interior logistic quantiles increase strictly with the probability level. -/
theorem strictMonoOn_quantile_logisticMeasure (hs : 0 < s) :
    StrictMonoOn (logisticMeasure m s).quantile (Ioo 0 1) :=
  Measure.strictMonoOn_quantile _ (continuous_cdf_logisticMeasure hs m)

/-- The logistic quantile is continuous on the interior probability levels. -/
theorem continuousOn_quantile_logisticMeasure (hs : 0 < s) :
    ContinuousOn (logisticMeasure m s).quantile (Ioo 0 1) :=
  Measure.continuousOn_quantile _
    ((strictMono_cdf_logisticMeasure hs m).strictMonoOn _)

/-- Logistic quantiles tend to minus infinity as the level decreases to zero. -/
theorem tendsto_quantile_logisticMeasure_nhdsGT_zero (hs : 0 < s) :
    Tendsto (fun u ↦ ((logisticMeasure m s).quantile u : EReal))
      (𝓝[>] 0) (𝓝 ⊥) :=
  Measure.tendsto_quantile_nhdsGT_zero_of_cdf_pos _ fun x ↦
    (cdf_nonneg _ (x - 1)).trans_lt (strictMono_cdf_logisticMeasure hs m (by linarith))

/-- Logistic quantiles tend to plus infinity as the level increases to one. -/
theorem tendsto_quantile_logisticMeasure_nhdsLT_one (hs : 0 < s) :
    Tendsto (fun u ↦ ((logisticMeasure m s).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ⊤) :=
  Measure.tendsto_quantile_nhdsLT_one_of_cdf_lt_one _ fun x ↦
    (strictMono_cdf_logisticMeasure hs m (by linarith : x < x + 1)).trans_le
      (cdf_le_one _ (x + 1))

end TauCeti.Probability
