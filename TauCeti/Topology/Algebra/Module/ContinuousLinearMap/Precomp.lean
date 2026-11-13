/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Continuity of precomposition for the topology of bounded convergence

Mathlib bundles precomposition by a fixed continuous linear map as a continuous linear map
`ContinuousLinearMap.precomp`, which needs `ContinuousConstSMul` on the target. This file records
that the underlying map is continuous for the topology of bounded convergence without that
assumption.

## Main results

* `ContinuousLinearMap.continuous_precomp`: for `L : E →L[𝕜] F`, the map `f ↦ f ∘ L` on
  `F →L[𝕜] G` is continuous.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 E F G : Type*} [NormedField 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]
  [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [Module 𝕜 G]

/-- Precomposition by a fixed continuous linear map is continuous for the topology of bounded
convergence. This is the argument of `ContinuousLinearMap.precomp`, without the bundling that
needs `ContinuousConstSMul`. -/
theorem continuous_precomp (L : E →L[𝕜] F) :
    Continuous fun f : F →L[𝕜] G ↦ f.comp L := by
  let : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  have : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  refine isUniformEmbedding_toUniformOnFun.isEmbedding.continuous_iff.2 ?_
  have hmaps : Set.MapsTo (L '' ·) { S | Bornology.IsVonNBounded 𝕜 S }
      { S | Bornology.IsVonNBounded 𝕜 S } := fun _ hS ↦ hS.image L
  exact (UniformOnFun.precomp_uniformContinuous hmaps).continuous.comp
    isUniformEmbedding_toUniformOnFun.isEmbedding.continuous

end ContinuousLinearMap
