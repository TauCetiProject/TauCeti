/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Continuous pushforwards of probability measures

A continuous measurable map induces a continuous pushforward for the weak topologies on
probability measures. Both spaces need measurable opens, but their sigma algebras may be finer
than the Borel sigma algebras. This applies in particular to measurable coordinate projections
when the product topology has measurable opens.

`MeasureTheory.ProbabilityMeasure.continuous_map_of_measurable` extends Mathlib's
`MeasureTheory.ProbabilityMeasure.continuous_map` by making the map's measurability explicit
instead of requiring the target's measurable space to be Borel. Its proof uses the same
bounded-continuous-test-function characterization of weak convergence.
-/

public section

namespace MeasureTheory.ProbabilityMeasure

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace X] [OpensMeasurableSpace X]
  [TopologicalSpace Y] [OpensMeasurableSpace Y]

/-- A continuous measurable map induces a continuous pushforward of probability measures for
the weak topologies, even when the target's measurable space is finer than its Borel space. -/
@[fun_prop]
lemma continuous_map_of_measurable {f : X → Y} (hf : Continuous f) (hm : Measurable f) :
    Continuous (fun μ : ProbabilityMeasure X ↦ μ.map f) := by
  rw [continuous_iff_forall_continuous_lintegral]
  intro g
  have hmap (μ : ProbabilityMeasure X) :
      (∫⁻ y, g y ∂(μ.map f).toMeasure) = ∫⁻ x, g (f x) ∂μ.toMeasure := by
    rw [toMeasure_map, lintegral_map (by fun_prop) hm]
  simp_rw [hmap]
  exact continuous_lintegral_boundedContinuousFunction (g.compContinuous ⟨f, hf⟩)

end MeasureTheory.ProbabilityMeasure
