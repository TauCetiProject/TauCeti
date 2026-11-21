/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Precomposition for the topology of bounded convergence

Mathlib bundles precomposition by a fixed continuous linear map as a continuous linear map
`ContinuousLinearMap.precomp`, which needs `ContinuousConstSMul` on the target. This file records
that the underlying map is continuous for the topology of bounded convergence without that
assumption, identifies `ContinuousLinearEquiv.arrowCongr` along the identity on the target with
precomposition, and records naturality of canonical evaluation `ContinuousLinearMap.applyₗ` and
evaluation-compatible maps under double precomposition (`precomp G (precomp G u)`).

## Main results

* `ContinuousLinearMap.continuous_precomp`: for `L : E →L[𝕜] F`, the map `f ↦ f ∘ L` on
  `F →L[𝕜] G` is continuous.
* `ContinuousLinearMap.applyₗ_comp_precomp`, `ContinuousLinearMap.precomp_precomp_comp_applyₗ`:
  naturality of canonical evaluation with respect to the double strong transpose.
* `ContinuousLinearMap.precomp_precomp_comp_of_forall_apply_eq`,
  `ContinuousLinearMap.symm_comp_precomp_precomp_comp_of_forall_apply_eq`: intertwining and
  recovery of `u : E →L[𝕜] F` from maps agreeing pointwise with canonical evaluation.
* `ContinuousLinearEquiv.toContinuousLinearMap_arrowCongr_refl`: `e.arrowCongr (.refl 𝕜 G)` is
  `precomp G e.symm.toContinuousLinearMap`.
* `ContinuousLinearEquiv.arrowCongr_refl_apply_of_forall_apply_eq`,
  `ContinuousLinearEquiv.toLinearMap_arrowCongr_refl_of_forall_apply_eq`: when `e` agrees
  pointwise with canonical evaluation, `e.arrowCongr (.refl 𝕜 G)` agrees with canonical evaluation
  on `E →L[𝕜] G` (for `G = 𝕜`, the strong-dual reflexivity of Bourbaki, *Topological Vector
  Spaces*, Chapter IV, §3, no. 3).

## References

* N. Bourbaki, *Topological Vector Spaces*, Chapter IV, §3, no. 3.
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

section ApplyLinear

variable [ContinuousSMul 𝕜 E] [ContinuousSMul 𝕜 F] [ContinuousConstSMul 𝕜 G]

/-- **Naturality of canonical evaluation.** Composing canonical evaluation at `x` with
`precomp G u` gives canonical evaluation at `u x`. Together with `precomp_apply`, this lets
`simp` reduce `precomp G (precomp G u) (applyₗ G (RingHom.id 𝕜) x)` to
`applyₗ G (RingHom.id 𝕜) (u x)`. -/
@[simp]
theorem applyₗ_comp_precomp (u : E →L[𝕜] F) (x : E) :
    (applyₗ G (RingHom.id 𝕜) x).comp (precomp G u) = applyₗ G (RingHom.id 𝕜) (u x) := by
  ext ψ
  simp

/-- Linear-map form of the naturality of canonical evaluation under `precomp G (precomp G u)`. -/
theorem precomp_precomp_comp_applyₗ (u : E →L[𝕜] F) :
    (precomp G (precomp G u)).toLinearMap.comp (applyₗ G (RingHom.id 𝕜)) =
      (applyₗ G (RingHom.id 𝕜)).comp u.toLinearMap := by
  ext x ψ
  simp

end ApplyLinear

section EvaluationMaps

variable [ContinuousConstSMul 𝕜 G]

/-- Any two continuous linear maps `E → (E →L[𝕜] G) →L[𝕜] G` and `F → (F →L[𝕜] G) →L[𝕜] G` that
agree pointwise with canonical evaluation intertwine `u : E →L[𝕜] F` with its double transpose
`precomp G (precomp G u)`; for `G = 𝕜` these are maps into the strong biduals. -/
theorem precomp_precomp_comp_of_forall_apply_eq (u : E →L[𝕜] F)
    {e₁ : E →L[𝕜] (E →L[𝕜] G) →L[𝕜] G} {e₂ : F →L[𝕜] (F →L[𝕜] G) →L[𝕜] G}
    (he₁ : ∀ x (φ : E →L[𝕜] G), e₁ x φ = φ x)
    (he₂ : ∀ y (ψ : F →L[𝕜] G), e₂ y ψ = ψ y) :
    (precomp G (precomp G u)).comp e₁ = e₂.comp u := by
  ext x ψ
  simp [he₁, he₂]

/-- When `E` and `F` carry topological linear isomorphisms with `(E →L[𝕜] G) →L[𝕜] G` and
`(F →L[𝕜] G) →L[𝕜] G` (for `G = 𝕜`, their strong biduals) agreeing with canonical evaluation,
conjugating the double transpose `precomp G (precomp G u)` by these isomorphisms recovers `u`. -/
theorem symm_comp_precomp_precomp_comp_of_forall_apply_eq (u : E →L[𝕜] F)
    {e₁ : E ≃L[𝕜] (E →L[𝕜] G) →L[𝕜] G} {e₂ : F ≃L[𝕜] (F →L[𝕜] G) →L[𝕜] G}
    (he₁ : ∀ x (φ : E →L[𝕜] G), e₁ x φ = φ x)
    (he₂ : ∀ y (ψ : F →L[𝕜] G), e₂ y ψ = ψ y) :
    e₂.symm.toContinuousLinearMap.comp
      ((precomp G (precomp G u)).comp e₁.toContinuousLinearMap) = u := by
  ext x
  rw [comp_apply, comp_apply, ContinuousLinearEquiv.coe_coe, e₂.symm_apply_eq]
  ext ψ
  simp [he₁, he₂]

end EvaluationMaps

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

/-- If `e : E ≃L[𝕜] (E →L[𝕜] G) →L[𝕜] G` agrees pointwise with canonical evaluation, then
`e.arrowCongr (.refl 𝕜 G)` agrees pointwise with canonical evaluation on `E →L[𝕜] G`. For `G = 𝕜`,
`e` is a strong-bidual isomorphism and `e.arrowCongr (.refl 𝕜 𝕜)` is the inverse of its strong
transpose. -/
theorem arrowCongr_refl_apply_of_forall_apply_eq (e : E ≃L[𝕜] (E →L[𝕜] G) →L[𝕜] G)
    (he : ∀ x (φ : E →L[𝕜] G), e x φ = φ x) (φ : E →L[𝕜] G) (Ψ : (E →L[𝕜] G) →L[𝕜] G) :
    e.arrowCongr (.refl 𝕜 G) φ Ψ = Ψ φ := by
  rw [arrowCongr_apply, refl_apply, ← he (e.symm Ψ) φ, e.apply_symm_apply]

/-- If `e : E ≃L[𝕜] (E →L[𝕜] G) →L[𝕜] G` agrees pointwise with canonical evaluation, then the
underlying linear map of `e.arrowCongr (.refl 𝕜 G)` is canonical evaluation on `E →L[𝕜] G`; for
`G = 𝕜`, the inverse of the strong transpose of a canonical bidual isomorphism is the canonical
bidual evaluation map of `StrongDual 𝕜 E`. -/
theorem toLinearMap_arrowCongr_refl_of_forall_apply_eq [ContinuousSMul 𝕜 G]
    (e : E ≃L[𝕜] (E →L[𝕜] G) →L[𝕜] G) (he : ∀ x (φ : E →L[𝕜] G), e x φ = φ x) :
    (e.arrowCongr (.refl 𝕜 G)).toLinearMap = ContinuousLinearMap.applyₗ G (RingHom.id 𝕜) := by
  ext φ Ψ
  exact e.arrowCongr_refl_apply_of_forall_apply_eq he φ Ψ

end ContinuousLinearEquiv
