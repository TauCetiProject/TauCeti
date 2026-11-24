/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Weak convergence on countable discrete spaces

For probability measures on a countable discrete space, weak convergence along any filter is
equivalent to convergence of every singleton mass. Consequently, continuity of a
probability-valued family on any topological parameter space can be checked one mass at a time.
The limit must itself be a probability measure; pointwise convergence to zero masses does not
suffice.

These criteria specialize Mathlib's portmanteau theorem and
`IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem` to singleton neighborhoods. The latter
asks for a countably generated filter; no such restriction is needed here, because the
convergence of all singleton masses is itself described by a countably generated filter.
-/

public section

open Filter Set Topology

namespace MeasureTheory.ProbabilityMeasure

variable {Ω ι X : Type*} [Countable Ω] [TopologicalSpace Ω] [DiscreteTopology Ω]
  [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- Weak convergence on a countable discrete space is exactly pointwise convergence of masses. -/
theorem tendsto_iff_forall_tendsto_singleton {μ : ι → ProbabilityMeasure Ω}
    {ν : ProbabilityMeasure Ω} {l : Filter ι} :
    Tendsto μ l (𝓝 ν) ↔ ∀ x, Tendsto (fun i ↦ μ i {x}) l (𝓝 (ν {x})) := by
  refine ⟨fun h x ↦ tendsto_measure_of_isClopen_of_tendsto h (isClopen_discrete _),
    fun h ↦ ?_⟩
  have hS : IsPiSystem (range fun x : Ω ↦ ({x} : Set Ω)) := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ ⟨z, hz, hz'⟩
    obtain rfl : x = y := (mem_singleton_iff.mp hz).symm.trans (mem_singleton_iff.mp hz')
    exact ⟨x, (inter_self _).symm⟩
  -- `L` is the coarsest filter along which every singleton mass tends to that of `ν`. It is
  -- countably generated since `Ω` is countable, so the π-system criterion shows that it
  -- converges to `ν`; and `μ` tends to `L` along `l` by `h`.
  let L := ⨅ x, comap (fun m : ProbabilityMeasure Ω ↦ m {x}) (𝓝 (ν {x}))
  have hL : Tendsto id L (𝓝 ν) := hS.tendsto_probabilityMeasure_of_tendsto_of_mem
    (fun _ _ ↦ .of_discrete)
    (fun _ _ x hx ↦ ⟨{x}, mem_range_self x, mem_nhds_discrete.2 (mem_singleton x),
      singleton_subset_iff.mpr hx⟩)
    (forall_mem_range.2 fun x ↦ tendsto_iInf' x tendsto_comap)
  exact hL.comp (tendsto_iInf.2 fun x ↦ tendsto_comap_iff.2 (h x))

/-- A probability-valued family on a countable discrete space is weakly continuous exactly
when all its singleton masses are continuous. -/
theorem continuous_iff_forall_continuous_singleton [TopologicalSpace X]
    {μ : X → ProbabilityMeasure Ω} :
    Continuous μ ↔ ∀ x, Continuous fun p ↦ μ p {x} := by
  simp only [continuous_iff_continuousAt, ContinuousAt, tendsto_iff_forall_tendsto_singleton]
  exact forall_comm

end MeasureTheory.ProbabilityMeasure
