/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Cdf
public import TauCeti.Probability.Distributions.Stable.Smooth
import TauCeti.Probability.Cdf.Density
import TauCeti.Probability.Distributions.Dirac

/-!
# Cumulative distribution functions of scalar stable laws

A scalar stable law of positive scale is absolutely continuous, with the Fourier-inversion
density `stablePDFReal`. Consequently its cumulative distribution function is the integral of
that density over a left half-line, and its derivative is the density at every real point. Since
the stable density is smooth, so is the cumulative distribution function.

The zero-scale law is a point mass at its location.

These results provide the analytic cdf interface used to obtain strict increase and quantiles
once positivity on the interior of the stable law's support is known.

## Main results

* `TauCeti.Probability.cdf_stableMeasure_eq_integral` expresses the cdf as the integral of the
  stable density;
* `TauCeti.Probability.hasDerivAt_cdf_stableMeasure` identifies its derivative pointwise;
* `TauCeti.Probability.contDiff_cdf_stableMeasure` proves that the cdf is smooth;
* `TauCeti.Probability.cdf_stableMeasure_zero_scale` gives the atomic boundary formula.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, sections 1.2 and 3.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ContDiff ENNReal NNReal

namespace TauCeti.Probability

variable {α β : ℝ} {s : ℝ≥0} {m : ℝ}

private theorem stableMeasure_eq_withDensity_ofReal (α β : ℝ) (hs : 0 < s) (m : ℝ) :
    stableMeasure α β s m =
      volume.withDensity fun x ↦ ENNReal.ofReal (stablePDFReal α β s m x) := by
  rw [stableMeasure_eq_withDensity α β hs, funext (stablePDF_eq_ofReal α β s m)]

/-- The cdf of a positive-scale stable law is the integral of its Fourier-inversion density over
the left half-line. -/
theorem cdf_stableMeasure_eq_integral (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1) (hs : 0 < s)
    (x : ℝ) :
    cdf (stableMeasure α β s m) x =
      ∫ y in Iic x, stablePDFReal α β s m y := by
  let _ := isProbabilityMeasure_stableMeasure hα hβ s m
  have hμ := stableMeasure_eq_withDensity_ofReal α β hs m
  rw [cdf_eq_real, hμ]
  exact measureReal_withDensity_ofReal
    (ae_restrict_of_ae (ae_of_all volume fun y ↦ stablePDFReal_nonneg α β s m y))
    measurableSet_Iic
    (integrable_stablePDFReal α β s m).integrableOn

/-- The cdf of a positive-scale stable law is differentiable at every point, with derivative its
Fourier-inversion density. -/
theorem hasDerivAt_cdf_stableMeasure (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1) (hs : 0 < s)
    (x : ℝ) :
    HasDerivAt (cdf (stableMeasure α β s m)) (stablePDFReal α β s m x) x := by
  let _ := isProbabilityMeasure_stableMeasure hα hβ s m
  exact hasDerivAt_cdf_of_eq_withDensity
    (stableMeasure_eq_withDensity_ofReal α β hs m)
    (measurable_stablePDFReal α β s m).aemeasurable
    (ae_of_all volume fun y ↦ stablePDFReal_nonneg α β s m y)
    (continuous_stablePDFReal α β s m).continuousAt

/-- The cdf of a positive-scale stable law is smooth. -/
theorem contDiff_cdf_stableMeasure (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1) (hs : 0 < s) :
    ContDiff ℝ ∞ (cdf (stableMeasure α β s m)) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x ↦ (hasDerivAt_cdf_stableMeasure hα hβ hs x).differentiableAt, ?_⟩
  have hderiv : deriv (cdf (stableMeasure α β s m)) = stablePDFReal α β s m := by
    funext x
    exact (hasDerivAt_cdf_stableMeasure hα hβ hs x).deriv
  rw [hderiv]
  exact contDiff_stablePDFReal α β s m

/-- The cdf of a positive-scale stable law is continuous. -/
theorem continuous_cdf_stableMeasure (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1) (hs : 0 < s) :
    Continuous (cdf (stableMeasure α β s m)) :=
  (contDiff_cdf_stableMeasure hα hβ hs).continuous

/-- At zero scale, a valid stable law has the cdf of the point mass at its location. -/
theorem cdf_stableMeasure_zero_scale (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1) (m x : ℝ) :
    cdf (stableMeasure α β 0 m) x = if m ≤ x then 1 else 0 := by
  rw [stableMeasure_zero_scale hα hβ, cdf_dirac]

end TauCeti.Probability
