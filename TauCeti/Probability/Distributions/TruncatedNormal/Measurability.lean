/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.TruncatedNormal.Basic
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# Parameter measurability of truncated normal laws

Truncated Gaussian laws are jointly measurable in their Gaussian parameters and their truncation
events whenever the events have a measurable incidence set. This allows random truncation bounds
and Gaussian parameters to define measure-valued kernels. The interval specializations use extended
real bounds and retain all four endpoint conventions, including at zero variance. Empty intervals
and events of zero Gaussian mass give the zero measure without additional hypotheses.

The named real and extended densities are jointly measurable as well. At zero variance they
vanish, as in their definitions; they do not represent a surviving Dirac mass.

## Main results

* `TauCeti.Probability.measurable_truncatedNormalMeasure` — arbitrary measurable incidence sets;
* `TauCeti.Probability.measurable_truncatedNormalMeasure_Ioc` and its `Icc`, `Ioo`, `Ico`
  counterparts — joint measurability in location, variance and extended interval bounds;
* `TauCeti.Probability.measurable_uncurry_truncatedNormalPDFReal`,
  `TauCeti.Probability.measurable_uncurry_truncatedNormalPDF` — joint density measurability.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley (1994), Chapter 13.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α] {m : α → ℝ} {v : α → ℝ≥0} {s : α → Set ℝ}

/-- Truncated Gaussian measures are measurable in the Gaussian parameters and the truncation
event, provided the event has a measurable incidence set. This includes zero variance and
conditioning events of zero mass. -/
@[fun_prop]
theorem measurable_truncatedNormalMeasure (hm : Measurable m) (hv : Measurable v)
    (hs : MeasurableSet {p : α × ℝ | p.2 ∈ s p.1}) :
    Measurable fun a => truncatedNormalMeasure (m a) (v a) (s a) := by
  simp only [truncatedNormalMeasure_def]
  exact (measurable_gaussianReal.comp (hm.prodMk hv)).cond_of_finite
    (fun a => inferInstanceAs (IsFiniteMeasure (gaussianReal (m a) (v a)))) hs

/-- The real truncated normal density is jointly measurable in its Gaussian parameters, its
truncation event and its evaluation point, for a measurable incidence set. -/
@[fun_prop]
theorem measurable_uncurry_truncatedNormalPDFReal (hm : Measurable m) (hv : Measurable v)
    (hs : MeasurableSet {p : α × ℝ | p.2 ∈ s p.1}) :
    Measurable fun p : α × ℝ => truncatedNormalPDFReal (m p.1) (v p.1) (s p.1) p.2 := by
  let κ : Kernel α ℝ := ⟨fun a => gaussianReal (m a) (v a),
    measurable_gaussianReal.comp (hm.prodMk hv)⟩
  have hmass : Measurable fun a => gaussianReal (m a) (v a) (s a) :=
    Kernel.measurable_kernel_prodMk_left_of_finite (κ := κ) hs
      (fun a => inferInstanceAs (IsFiniteMeasure (gaussianReal (m a) (v a))))
  have hpdf : Measurable fun p : α × ℝ => gaussianPDFReal (m p.1) (v p.1) p.2 := by
    fun_prop
  convert (hpdf.indicator hs).div ((hmass.comp measurable_fst).ennreal_toReal) using 1
  ext p
  simp [truncatedNormalPDFReal_def, measureReal_def, Set.indicator]

/-- The extended truncated normal density is jointly measurable in its Gaussian parameters,
truncation event and evaluation point, for a measurable incidence set. -/
@[fun_prop]
theorem measurable_uncurry_truncatedNormalPDF (hm : Measurable m) (hv : Measurable v)
    (hs : MeasurableSet {p : α × ℝ | p.2 ∈ s p.1}) :
    Measurable fun p : α × ℝ => truncatedNormalPDF (m p.1) (v p.1) (s p.1) p.2 := by
  simpa only [truncatedNormalPDF_eq_ofReal] using
    (measurable_uncurry_truncatedNormalPDFReal hm hv hs).ennreal_ofReal

/-- Gaussian truncation to `(l, r]` is jointly measurable in location, variance and extended
endpoints, including empty or reversed intervals. -/
@[fun_prop]
theorem measurable_truncatedNormalMeasure_Ioc :
    Measurable fun p : ℝ × ℝ≥0 × EReal × EReal =>
      truncatedNormalMeasure p.1 p.2.1 (Real.toEReal ⁻¹' Ioc p.2.2.1 p.2.2.2) := by
  apply measurable_truncatedNormalMeasure (by fun_prop) (by fun_prop)
  measurability

/-- Gaussian truncation to `[l, r]` is jointly measurable in location, variance and extended
endpoints. At zero variance, a retained endpoint atom is included. -/
@[fun_prop]
theorem measurable_truncatedNormalMeasure_Icc :
    Measurable fun p : ℝ × ℝ≥0 × EReal × EReal =>
      truncatedNormalMeasure p.1 p.2.1 (Real.toEReal ⁻¹' Icc p.2.2.1 p.2.2.2) := by
  apply measurable_truncatedNormalMeasure (by fun_prop) (by fun_prop)
  measurability

/-- Gaussian truncation to `(l, r)` is jointly measurable in location, variance and extended
endpoints, retaining the exclusion of both endpoint atoms. -/
@[fun_prop]
theorem measurable_truncatedNormalMeasure_Ioo :
    Measurable fun p : ℝ × ℝ≥0 × EReal × EReal =>
      truncatedNormalMeasure p.1 p.2.1 (Real.toEReal ⁻¹' Ioo p.2.2.1 p.2.2.2) := by
  apply measurable_truncatedNormalMeasure (by fun_prop) (by fun_prop)
  measurability

/-- Gaussian truncation to `[l, r)` is jointly measurable in location, variance and extended
endpoints, retaining the inclusion of the lower atom and exclusion of the upper atom. -/
@[fun_prop]
theorem measurable_truncatedNormalMeasure_Ico :
    Measurable fun p : ℝ × ℝ≥0 × EReal × EReal =>
      truncatedNormalMeasure p.1 p.2.1 (Real.toEReal ⁻¹' Ico p.2.2.1 p.2.2.2) := by
  apply measurable_truncatedNormalMeasure (by fun_prop) (by fun_prop)
  measurability

end TauCeti.Probability
