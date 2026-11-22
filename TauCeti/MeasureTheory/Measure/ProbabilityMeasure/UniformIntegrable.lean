/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import TauCeti.MeasureTheory.Measure.FiniteMeasure.UniformIntegrable

/-!
# Integrals at weak cluster points of probability measures

The finite-measure square-bound criterion applies to probability measures via the continuous
embedding into finite measures. Thus a continuous function whose integrals converge and whose
square is eventually integrable with uniformly bounded integral remains integrable at every weak
cluster point, where its integral has the same limit.
-/

public section

open Filter MeasureTheory Topology

namespace MeasureTheory.ProbabilityMeasure

/-- An eventual square-integrability bound transfers integrability and the limit of integrals of
a continuous function to every weak cluster point of the probability measures. -/
theorem integrable_and_integral_eq_of_mapClusterPt_of_integral_sq_le
    {Ω : Type*} [PseudoMetricSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    {ι : Type*} {l : Filter ι} {μn : ι → ProbabilityMeasure Ω}
    {ν : ProbabilityMeasure Ω} {g : Ω → ℝ} {m B : ℝ}
    (hg : Continuous g)
    (h2 : ∀ᶠ i in l, Integrable (fun x ↦ g x ^ 2) (μn i : Measure Ω))
    (hB : ∀ᶠ i in l, ∫ x, g x ^ 2 ∂(μn i : Measure Ω) ≤ B)
    (hlim : Tendsto (fun i ↦ ∫ x, g x ∂(μn i : Measure Ω)) l (𝓝 m))
    (hν : MapClusterPt ν l μn) :
    Integrable g (ν : Measure Ω) ∧ ∫ x, g x ∂(ν : Measure Ω) = m := by
  have hν' := hν.continuousAt_comp toFiniteMeasure_continuous.continuousAt
  have h2' : ∀ᶠ i in l, Integrable (fun x ↦ g x ^ 2) ((μn i).toFiniteMeasure : Measure Ω) := by
    simpa only [toMeasure_comp_toFiniteMeasure_eq_toMeasure] using h2
  have hB' : ∀ᶠ i in l, ∫ x, g x ^ 2 ∂((μn i).toFiniteMeasure : Measure Ω) ≤ B := by
    simpa only [toMeasure_comp_toFiniteMeasure_eq_toMeasure] using hB
  have hlim' : Tendsto (fun i ↦ ∫ x, g x ∂((μn i).toFiniteMeasure : Measure Ω)) l (𝓝 m) := by
    simpa only [toMeasure_comp_toFiniteMeasure_eq_toMeasure] using hlim
  simpa only [toMeasure_comp_toFiniteMeasure_eq_toMeasure, Function.comp_apply] using
    FiniteMeasure.integrable_and_integral_eq_of_mapClusterPt_of_integral_sq_le
      hg h2' hB' hlim' hν'

end MeasureTheory.ProbabilityMeasure
