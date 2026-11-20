/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Weak topology on probability measures

`MeasureTheory.ProbabilityMeasure.isInducing_integral_boundedContinuousFunction` identifies
the weak topology on probability measures with the topology induced by all bounded continuous
real test integrals. This provides a common interface for other families of tests determining
weak convergence.
-/

public section

open Filter Topology
open scoped Topology BoundedContinuousFunction

namespace MeasureTheory.ProbabilityMeasure

/-- Bounded continuous real test integrals induce the weak topology on probability measures. -/
theorem isInducing_integral_boundedContinuousFunction
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] :
    IsInducing (fun ν : ProbabilityMeasure X ↦
      fun f : X →ᵇ ℝ ↦ ∫ x, f x ∂(ν : Measure X)) := by
  apply isInducing_iff_nhds.2
  intro ν
  apply le_antisymm
  · exact (continuous_pi continuous_integral_boundedContinuousFunction).continuousAt.le_comap
  · exact tendsto_iff_forall_integral_tendsto.2 fun f ↦
      ((continuous_apply f).tendsto (fun g : X →ᵇ ℝ ↦ ∫ x, g x ∂(ν : Measure X))).comp
        tendsto_comap

end MeasureTheory.ProbabilityMeasure
