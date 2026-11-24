/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Topology.UniformSpace.Cauchy
public import Mathlib.Topology.UniformSpace.CompleteSeparated

/-!
# Completeness transfer between uniformities

A continuous identity transfers limits of Cauchy sequences from a complete reference uniformity.
A countable basis for the target uniformity allows this sequential criterion to imply completeness.
-/

public section

namespace UniformSpace

open Filter
open scoped Topology

variable {X : Type*}

/-- A countably generated target uniformity is complete if the identity from a complete
reference uniformity is continuous and every target Cauchy sequence is reference Cauchy. -/
theorem completeSpace_of_continuous_cauchySeq
    (u₀ u₁ : UniformSpace X)
    [@IsCountablyGenerated _ (@uniformity X u₁)]
    (hcomplete : @CompleteSpace X u₀)
    (hcontinuous : @Continuous X X u₀.toTopologicalSpace
      u₁.toTopologicalSpace id)
    (hcauchy : ∀ u : ℕ → X, @CauchySeq X ℕ u₁ _ u →
      @CauchySeq X ℕ u₀ _ u) :
    @CompleteSpace X u₁ := by
  let : UniformSpace X := u₁
  apply UniformSpace.complete_of_cauchySeq_tendsto
  intro u hu
  have hlimit : ∃ x, Tendsto u atTop
      (@nhds X u₀.toTopologicalSpace x) := by
    let : UniformSpace X := u₀
    let : CompleteSpace X := hcomplete
    exact cauchySeq_tendsto_of_complete (hcauchy u hu)
  obtain ⟨x, hx⟩ := hlimit
  exact ⟨x, (@Continuous.tendsto X X u₀.toTopologicalSpace
    u₁.toTopologicalSpace id hcontinuous x).comp hx⟩

end UniformSpace

namespace Topology.IsClosedEmbedding

open Filter Set
open scoped Topology

/-- A uniformly continuous closed embedding into a complete uniform space has complete domain. -/
theorem completeSpace_of_uniformContinuous {α β : Type*} [UniformSpace α] [UniformSpace β]
    [CompleteSpace β] {ι : α → β} (hι : IsClosedEmbedding ι) (hu : UniformContinuous ι) :
    CompleteSpace α := by
  refine ⟨fun {l} hl ↦ ?_⟩
  have : NeBot l := hl.1
  obtain ⟨y, hy⟩ := CompleteSpace.complete (hl.map hu)
  have hyr : y ∈ range ι := hι.isClosed_range.mem_of_tendsto hy
    (Eventually.of_forall fun x ↦ mem_range_self x)
  obtain ⟨x, rfl⟩ := hyr
  exact ⟨x, hι.isEmbedding.isInducing.tendsto_nhds_iff.mpr hy⟩

end Topology.IsClosedEmbedding
