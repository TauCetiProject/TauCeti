/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Weak convergence on countable discrete spaces

For probability measures on a countable discrete space, weak convergence is equivalent to
convergence of every singleton mass. Consequently, continuity of a probability-valued family
on a sequential parameter space can be checked one mass at a time. The limit must itself be
a probability measure; pointwise convergence to zero masses does not suffice.

These criteria specialize Mathlib's portmanteau theorem and
`IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem` to singleton neighborhoods.
-/

public section

open Filter Set Topology

namespace MeasureTheory.ProbabilityMeasure

variable {Ω ι X : Type*} [Countable Ω] [TopologicalSpace Ω] [DiscreteTopology Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Weak convergence on a countable discrete space is exactly pointwise convergence of masses. -/
theorem tendsto_iff_forall_tendsto_singleton {μ : ι → ProbabilityMeasure Ω}
    {ν : ProbabilityMeasure Ω} {l : Filter ι} [l.IsCountablyGenerated] :
    Tendsto μ l (𝓝 ν) ↔ ∀ x, Tendsto (fun i ↦ μ i {x}) l (𝓝 (ν {x})) := by
  constructor
  · intro h x
    exact tendsto_measure_of_isClopen_of_tendsto h ⟨isClosed_discrete _, isOpen_discrete _⟩
  intro h
  have hS : IsPiSystem (range fun x : Ω ↦ ({x} : Set Ω)) := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ ⟨z, hz, hz'⟩
    have hxy : x = y := (mem_singleton_iff.mp hz).symm.trans (mem_singleton_iff.mp hz')
    exact ⟨x, by simp [hxy]⟩
  apply hS.tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro _ ⟨x, rfl⟩
    exact measurableSet_singleton x
  · intro u _ x hx
    exact ⟨{x}, ⟨x, rfl⟩, (isOpen_discrete _).mem_nhds (mem_singleton x),
      singleton_subset_iff.mpr hx⟩
  · rintro _ ⟨x, rfl⟩
    exact h x

/-- A probability-valued family on a sequential parameter space is weakly continuous exactly
when all its singleton masses are continuous. -/
theorem continuous_iff_forall_continuous_singleton [TopologicalSpace X] [SequentialSpace X]
    {μ : X → ProbabilityMeasure Ω} :
    Continuous μ ↔ ∀ x, Continuous fun p ↦ μ p {x} := by
  constructor
  · intro h x
    apply continuous_iff_seqContinuous.2
    intro p a hp
    exact (tendsto_iff_forall_tendsto_singleton.1 ((h.tendsto a).comp hp)) x
  · intro h
    apply continuous_iff_seqContinuous.2
    intro p a hp
    exact tendsto_iff_forall_tendsto_singleton.2 fun x ↦ ((h x).tendsto a).comp hp

end MeasureTheory.ProbabilityMeasure
