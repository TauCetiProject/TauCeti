/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Stable.Cdf
public import TauCeti.Probability.Distributions.Stable.Support
public import TauCeti.Probability.Quantile

/-!
# Quantiles of two-sided stable laws

For a positive-scale stable law with strict interior skewness `|β| < 1`, the cdf is strictly
increasing on the whole real line. Every interior probability level therefore has a unique
real cdf root, given by `Measure.quantile`. The quantile is continuous and strictly increasing
on `(0, 1)`, tending to minus and plus infinity at the respective endpoints.

Strict increase of the quantile itself only needs absence of atoms, so that result also covers
full skewness. No root uniqueness or infinite-endpoint assertion is made for full-skewness
non-Gaussian laws.

The cdf strict-increase argument uses the full-support theorem
`support_stableMeasure_of_abs_lt_one`; the remaining statements specialize the general
measure-level quantile API.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1 and section 3.2.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped NNReal

namespace TauCeti.Probability

variable {α β : ℝ} {s : ℝ≥0} {m u x : ℝ}

/-- A positive-scale stable cdf with strict interior skewness is strictly increasing on `ℝ`,
including at shapes one and two. -/
theorem strictMono_cdf_stableMeasure_of_abs_lt_one (hα : α ∈ Ioc 0 2) (hβ : |β| < 1)
    (hs : 0 < s) (m : ℝ) : StrictMono (cdf (stableMeasure α β s m)) := by
  let := isProbabilityMeasure_stableMeasure hα hβ.le s m
  have hmono := Measure.strictMonoOn_cdf_of_subset_support (stableMeasure α β s m)
    ordConnected_univ (by rw [support_stableMeasure_of_abs_lt_one hα hβ hs m])
  exact fun _ _ hxy ↦ hmono (mem_univ _) (mem_univ _) hxy

/-- For positive scale and strict interior skewness, the stable quantile is characterized as
the unique real root of its cdf equation at each interior probability level. -/
theorem quantile_stableMeasure_eq_iff_of_abs_lt_one (hα : α ∈ Ioc 0 2) (hβ : |β| < 1)
    (hs : 0 < s) (hu : u ∈ Ioo 0 1) :
    (stableMeasure α β s m).quantile u = x ↔ cdf (stableMeasure α β s m) x = u := by
  let := isProbabilityMeasure_stableMeasure hα hβ.le s m
  simpa using Measure.quantile_eq_iff_of_ae_mem_of_strictMonoOn _ ordConnected_univ
    (ae_of_all _ mem_univ) (continuous_cdf_stableMeasure hα hβ.le hs)
    ((strictMono_cdf_stableMeasure_of_abs_lt_one hα hβ hs m).strictMonoOn _) hu

/-- For every valid skewness, a positive-scale stable quantile is strictly increasing on
interior levels, even when the distribution is supported on a half-line. -/
theorem strictMonoOn_quantile_stableMeasure (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1)
    (hs : 0 < s) (m : ℝ) : StrictMonoOn (stableMeasure α β s m).quantile (Ioo 0 1) := by
  let := isProbabilityMeasure_stableMeasure hα hβ s m
  exact Measure.strictMonoOn_quantile _ (continuous_cdf_stableMeasure hα hβ hs)

/-- Two-sided positive-scale stable quantiles vary continuously with interior probability
levels. -/
theorem continuousOn_quantile_stableMeasure_of_abs_lt_one (hα : α ∈ Ioc 0 2)
    (hβ : |β| < 1) (hs : 0 < s) (m : ℝ) :
    ContinuousOn (stableMeasure α β s m).quantile (Ioo 0 1) := by
  let := isProbabilityMeasure_stableMeasure hα hβ.le s m
  exact Measure.continuousOn_quantile_of_strictMonoOn _ ordConnected_univ
    ((strictMono_cdf_stableMeasure_of_abs_lt_one hα hβ hs m).strictMonoOn _)
    (mapsTo_univ _ _)

/-- Two-sided positive-scale stable quantiles tend to minus infinity as the level decreases
to zero. This is a one-sided limit, not a value of the totalized quantile at zero. -/
theorem tendsto_quantile_stableMeasure_nhdsGT_zero_of_abs_lt_one (hα : α ∈ Ioc 0 2)
    (hβ : |β| < 1) (hs : 0 < s) (m : ℝ) :
    Tendsto (fun u ↦ ((stableMeasure α β s m).quantile u : EReal))
      (𝓝[>] 0) (𝓝 ⊥) := by
  let := isProbabilityMeasure_stableMeasure hα hβ.le s m
  exact Measure.tendsto_quantile_nhdsGT_zero_of_strictMono_cdf _
    (strictMono_cdf_stableMeasure_of_abs_lt_one hα hβ hs m)

/-- Two-sided positive-scale stable quantiles tend to plus infinity as the level increases
to one. This is a one-sided limit, not a value of the totalized quantile at one. -/
theorem tendsto_quantile_stableMeasure_nhdsLT_one_of_abs_lt_one (hα : α ∈ Ioc 0 2)
    (hβ : |β| < 1) (hs : 0 < s) (m : ℝ) :
    Tendsto (fun u ↦ ((stableMeasure α β s m).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ⊤) := by
  let := isProbabilityMeasure_stableMeasure hα hβ.le s m
  exact Measure.tendsto_quantile_nhdsLT_one_of_strictMono_cdf _
    (strictMono_cdf_stableMeasure_of_abs_lt_one hα hβ hs m)

end TauCeti.Probability
