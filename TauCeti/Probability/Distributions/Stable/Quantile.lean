/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Stable.Cdf
public import TauCeti.Probability.Distributions.Stable.Support
public import TauCeti.Probability.Quantile
import TauCeti.Probability.Cdf.Density
import TauCeti.Probability.Distributions.Dirac

/-!
# Quantiles of two-sided stable laws

A stable law of positive scale and strict interior skewness has an everywhere positive density.
Its cdf is therefore continuous and strictly increasing on the whole real line. Consequently,
each interior quantile is the unique real root of the Fourier-inversion cdf, the quantile varies
continuously and strictly increasingly with its level, and its endpoint limits are minus and plus
infinity. At zero scale, every interior quantile equals the location of the point mass.

## Main results

* `TauCeti.Probability.strictMono_cdf_stableMeasure_of_abs_lt_one` proves strict increase of the
  cdf for positive scale and `|β| < 1`.
* `TauCeti.Probability.quantile_stableMeasure_eq_iff_of_abs_lt_one` characterizes each interior
  quantile as the unique root of the density-integral cdf.
* `TauCeti.Probability.strictMonoOn_quantile_stableMeasure` and
  `TauCeti.Probability.continuousOn_quantile_stableMeasure_of_abs_lt_one` give the regularity of
  the quantile function; strict increase holds for every valid skewness.
* `TauCeti.Probability.tendsto_quantile_stableMeasure_nhdsGT_zero_of_abs_lt_one` and
  `TauCeti.Probability.tendsto_quantile_stableMeasure_nhdsLT_one_of_abs_lt_one` give its endpoint
  limits.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, sections 1.2 and 3.2.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped NNReal

namespace TauCeti.Probability

variable {α β : ℝ} {s : ℝ≥0} {m u x : ℝ}

/-- The cdf of a positive-scale stable law with strict interior skewness is strictly increasing
on the whole real line. -/
theorem strictMono_cdf_stableMeasure_of_abs_lt_one (hα : α ∈ Ioc 0 2) (hβ : |β| < 1)
    (hs : 0 < s) (m : ℝ) : StrictMono (cdf (stableMeasure α β s m)) := by
  let _ := isProbabilityMeasure_stableMeasure hα hβ.le s m
  exact strictMono_cdf_of_eq_withDensity
    (stableMeasure_eq_withDensity_ofReal α β hs m)
    (measurable_stablePDFReal α β s m).aemeasurable
    (stablePDFReal_pos_of_abs_lt_one hα hβ hs m)

/-- Every interior quantile of a positive-scale stable law with strict interior skewness is the
unique real root of its Fourier-inversion cdf. -/
theorem quantile_stableMeasure_eq_iff_of_abs_lt_one (hα : α ∈ Ioc 0 2) (hβ : |β| < 1)
    (hs : 0 < s) (hu : u ∈ Ioo 0 1) :
    (stableMeasure α β s m).quantile u = x ↔
      ∫ y in Iic x, stablePDFReal α β s m y = u := by
  rw [← cdf_stableMeasure_eq_integral hα hβ.le hs]
  constructor
  · rintro rfl
    exact Measure.cdf_quantile _ (continuous_cdf_stableMeasure hα hβ.le hs) hu.1 hu.2
  · intro h
    rw [← h]
    exact Measure.quantile_cdf _
      ((strictMono_cdf_stableMeasure_of_abs_lt_one hα hβ hs m).strictMonoOn _)
      (by rw [h]; exact hu)

/-- Interior quantiles of every valid positive-scale stable law increase strictly with the
probability level. -/
theorem strictMonoOn_quantile_stableMeasure (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1)
    (hs : 0 < s) (m : ℝ) :
    StrictMonoOn (stableMeasure α β s m).quantile (Ioo 0 1) :=
  Measure.strictMonoOn_quantile _ (continuous_cdf_stableMeasure hα hβ hs)

/-- The quantile of a positive-scale stable law with strict interior skewness is continuous at
every interior probability level. -/
theorem continuousOn_quantile_stableMeasure_of_abs_lt_one (hα : α ∈ Ioc 0 2)
    (hβ : |β| < 1) (hs : 0 < s) (m : ℝ) :
    ContinuousOn (stableMeasure α β s m).quantile (Ioo 0 1) :=
  Measure.continuousOn_quantile _ (continuous_cdf_stableMeasure hα hβ.le hs)
    ((strictMono_cdf_stableMeasure_of_abs_lt_one hα hβ hs m).strictMonoOn _)

/-- Stable quantiles tend to minus infinity as the probability level tends to zero from above
when the scale is positive and the skewness is strictly interior. -/
theorem tendsto_quantile_stableMeasure_nhdsGT_zero_of_abs_lt_one (hα : α ∈ Ioc 0 2)
    (hβ : |β| < 1) (hs : 0 < s) (m : ℝ) :
    Tendsto (fun u ↦ ((stableMeasure α β s m).quantile u : EReal))
      (𝓝[>] 0) (𝓝 ⊥) :=
  Measure.tendsto_quantile_nhdsGT_zero_of_cdf_pos _ fun x ↦
    (cdf_nonneg _ (x - 1)).trans_lt
      (strictMono_cdf_stableMeasure_of_abs_lt_one hα hβ hs m (by linarith))

/-- Stable quantiles tend to plus infinity as the probability level tends to one from below when
the scale is positive and the skewness is strictly interior. -/
theorem tendsto_quantile_stableMeasure_nhdsLT_one_of_abs_lt_one (hα : α ∈ Ioc 0 2)
    (hβ : |β| < 1) (hs : 0 < s) (m : ℝ) :
    Tendsto (fun u ↦ ((stableMeasure α β s m).quantile u : EReal))
      (𝓝[<] 1) (𝓝 ⊤) :=
  Measure.tendsto_quantile_nhdsLT_one_of_cdf_lt_one _ fun x ↦
    (strictMono_cdf_stableMeasure_of_abs_lt_one hα hβ hs m
      (by linarith : x < x + 1)).trans_le (cdf_le_one _ (x + 1))

/-- Every interior quantile of a valid zero-scale stable law equals its location. -/
theorem quantile_stableMeasure_zero_scale (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1)
    (hu : u ∈ Ioo 0 1) (m : ℝ) : (stableMeasure α β 0 m).quantile u = m := by
  rw [stableMeasure_zero_scale hα hβ, Measure.quantile_dirac m hu.1 hu.2.le]

end TauCeti.Probability
