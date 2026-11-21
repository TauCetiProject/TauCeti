/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.SkewNormal.Basic

/-!
# Regularity and endpoint limits of skew-normal quantiles

For positive scale, the skew-normal quantile is continuous and strictly increasing on `(0, 1)`.
Its limits at zero from above and at one from below are minus and plus infinity, respectively,
expressed in `EReal`. These limits concern interior probability levels, not values of the
quantile's totalized definition at zero or one.

Together with `quantile_skewNormalMeasure_eq_iff`, these results describe the dependence of the
unique root of the Owen–T cdf equation on its probability level. They specialize the general
quantile theory using the continuous, strictly increasing skew-normal cdf.

## References

* A. Azzalini and A. Capitanio, *The Skew-Normal and Related Families*, Cambridge University
  Press, 2014.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace TauCeti.Probability

variable {s : ℝ}

/-- With positive scale, the skew-normal quantile is strictly increasing on interior levels. -/
theorem strictMonoOn_quantile_skewNormalMeasure (hs : 0 < s) (m α : ℝ) :
    StrictMonoOn (skewNormalMeasure m s α).quantile (Ioo 0 1) :=
  Measure.strictMonoOn_quantile _ (continuous_cdf_skewNormalMeasure hs m α)

/-- With positive scale, the skew-normal quantile is continuous on interior levels. -/
theorem continuousOn_quantile_skewNormalMeasure (hs : 0 < s) (m α : ℝ) :
    ContinuousOn (skewNormalMeasure m s α).quantile (Ioo 0 1) :=
  Measure.continuousOn_quantile _
    ((strictMono_cdf_skewNormalMeasure hs m α).strictMonoOn _)

/-- Skew-normal quantiles tend to minus infinity as the level tends to zero from above. -/
theorem tendsto_quantile_skewNormalMeasure_nhdsGT_zero (hs : 0 < s) (m α : ℝ) :
    Tendsto (fun u ↦ ((skewNormalMeasure m s α).quantile u : EReal))
      (𝓝[>] 0) (𝓝 ⊥) :=
  Measure.tendsto_quantile_nhdsGT_zero_of_strictMono_cdf _ (strictMono_cdf_skewNormalMeasure hs m α)

/-- Skew-normal quantiles tend to plus infinity as the level tends to one from below. -/
theorem tendsto_quantile_skewNormalMeasure_nhdsLT_one (hs : 0 < s) (m α : ℝ) :
    Tendsto (fun u ↦ ((skewNormalMeasure m s α).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ⊤) :=
  Measure.tendsto_quantile_nhdsLT_one_of_strictMono_cdf _ (strictMono_cdf_skewNormalMeasure hs m α)

end TauCeti.Probability
