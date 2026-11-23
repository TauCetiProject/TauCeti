/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Precomposition by a continuous linear map

Mathlib bundles precomposition by a fixed continuous linear map as a continuous linear map
`ContinuousLinearMap.precomp`, which needs `ContinuousConstSMul` on the target. This file records
that the underlying map is continuous for the topology of bounded convergence without that
assumption, that the bundled maps satisfy the identity and composition laws of a contravariant
functor (with target `G = 𝕜` these are the functoriality laws of the continuous dual), and
identifies `ContinuousLinearEquiv.arrowCongr` along the identity on the target with
precomposition.

## Main results

* `ContinuousLinearMap.continuous_precomp`: for `L : E →L[𝕜] F`, the map `f ↦ f ∘ L` on
  `F →L[𝕜] G` is continuous.
* `ContinuousLinearMap.precomp_id`, `ContinuousLinearMap.precomp_comp`: precomposition by the
  identity is the identity, and precomposition reverses composition.
* `ContinuousLinearEquiv.toContinuousLinearMap_arrowCongr_refl`: `e.arrowCongr (.refl 𝕜 G)` is
  `precomp G e.symm.toContinuousLinearMap`.
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

section Functoriality

variable [ContinuousConstSMul 𝕜 G]

/-- Precomposition by the identity map is the identity map. -/
@[simp]
theorem precomp_id :
    precomp G (ContinuousLinearMap.id 𝕜 E) = ContinuousLinearMap.id 𝕜 (E →L[𝕜] G) := by
  ext f x
  simp

/-- Precomposition reverses composition. -/
@[simp]
theorem precomp_comp {H : Type*} [AddCommGroup H] [TopologicalSpace H] [Module 𝕜 H]
    (T : E →L[𝕜] F) (S : F →L[𝕜] H) :
    precomp G (S.comp T) =
      (precomp G T : (F →L[𝕜] G) →L[𝕜] E →L[𝕜] G).comp (precomp G S) := by
  ext f x
  simp

end Functoriality

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable {𝕜 E F G : Type*} [NormedField 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]
  [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [Module 𝕜 G] [ContinuousConstSMul 𝕜 G]

/-- `e.arrowCongr (.refl 𝕜 G)` as a continuous linear map is precomposition with `e.symm`. -/
@[simp]
theorem toContinuousLinearMap_arrowCongr_refl (e : E ≃L[𝕜] F) :
    (e.arrowCongr (ContinuousLinearEquiv.refl 𝕜 G)).toContinuousLinearMap =
      ContinuousLinearMap.precomp G e.symm.toContinuousLinearMap := by
  ext f x
  simp

end ContinuousLinearEquiv
