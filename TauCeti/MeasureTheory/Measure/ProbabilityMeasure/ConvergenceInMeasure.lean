/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import TauCeti.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Weak convergence in measure to a deterministic law

For random probability measures, convergence in measure to a deterministic law in the weak
topology is equivalent to convergence in measure of every bounded continuous real test
integral. The neighborhood formulation works without selecting a metric on probability
measures, and allows the sample spaces and measures to vary with the index. It provides the
common interface for other families of tests determining weak convergence.

The result uses outer measures, so it needs no measurability of the random measures or events.
When the sample measures are probabilities, it expresses weak convergence in probability.
-/

public section

open Filter Topology
open scoped Topology BoundedContinuousFunction

namespace MeasureTheory.ProbabilityMeasure

/-- Convergence in measure to a deterministic law in the weak topology is equivalent to
convergence in measure of each real bounded continuous test integral. The sample spaces may
vary and no measurability or finiteness assumptions on their measures are needed. -/
theorem tendsto_measure_notMem_nhds_iff_integral
    {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (P : (i : ι) → Measure (Ω i)) (μs : (i : ι) → Ω i → ProbabilityMeasure X)
    (l : Filter ι) (μ : ProbabilityMeasure X) :
    (∀ U ∈ 𝓝 μ, Tendsto (fun i ↦ P i {ω | μs i ω ∉ U}) l (𝓝 0)) ↔
      ∀ f : X →ᵇ ℝ, ∀ ε : ℝ, 0 < ε → Tendsto (fun i ↦ P i {ω |
        ε ≤ |(∫ x, f x ∂(μs i ω : Measure X)) - ∫ x, f x ∂(μ : Measure X)|}) l (𝓝 0) := by
  have hT : IsInducing (fun ν : ProbabilityMeasure X ↦
      fun f : X →ᵇ ℝ ↦ ∫ x, f x ∂(ν : Measure X)) := by
    apply isInducing_iff_nhds.2
    intro ν
    apply le_antisymm
    · exact (continuous_pi continuous_integral_boundedContinuousFunction).continuousAt.le_comap
    · exact tendsto_iff_forall_integral_tendsto.2 fun f ↦
        ((continuous_apply f).tendsto (fun g : X →ᵇ ℝ ↦ ∫ x, g x ∂(ν : Measure X))).comp
          tendsto_comap
  simpa only [Real.dist_eq] using hT.tendsto_measure_notMem_nhds_iff P μs l μ

end MeasureTheory.ProbabilityMeasure
