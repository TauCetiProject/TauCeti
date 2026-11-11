/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
public import TauCeti.Geometry.Symplectic.Lagrangian.Opens
public import TauCeti.Geometry.Symplectic.Lagrangian.Prod
public import TauCeti.Geometry.Symplectic.Lagrangian.Rescale

/-!
# Lagrangian embeddings

A Lagrangian embedding is a smooth embedding whose tangent images are Lagrangian.
Unlike a Lagrangian immersion it is a homeomorphism onto its image, so it parametrizes an
embedded submanifold and excludes self-intersections. The definition uses the existing
smooth-immersion, topological-embedding and Lagrangian tangent-image predicates.

Reparametrization by a diffeomorphism, transport by a symplectomorphism, products, restriction
to an open subset of the source and nonzero rescaling of the form preserve Lagrangian embeddings,
and a map into an open submanifold is a Lagrangian embedding for the restricted form exactly when
its composition with the inclusion is one. In finite dimension an embedding is Lagrangian if its
tangent images are isotropic and its source has half the ambient dimension. For a nonempty source
this condition is also necessary. No global dimension condition is imposed on an empty embedding.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Section 3.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, Section 3.4.
-/

public noncomputable section

open Manifold Module TopologicalSpace
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N]
  {σ : SmoothTwoForm I M} {hσ : σ.IsNondegenerate} {f : N → M}

variable (hσ J) in
/-- A Lagrangian embedding is a smooth immersion, a topological embedding, and a map with
Lagrangian tangent images. In particular, its image has no self-intersections. -/
structure IsLagrangianEmbedding (f : N → M) : Prop where
  /-- The parametrization is a smooth immersion. -/
  isImmersion : Manifold.IsImmersion J I ∞ f
  /-- The parametrization is a homeomorphism onto its image. -/
  isEmbedding : Topology.IsEmbedding f
  /-- Every tangent image is a Lagrangian subspace. -/
  isLagrangianMap : hσ.IsLagrangianMap J f

/-- A Lagrangian embedding is a smooth embedding in Mathlib's sense. -/
theorem IsLagrangianEmbedding.isSmoothEmbedding (h : hσ.IsLagrangianEmbedding J f) :
    Manifold.IsSmoothEmbedding J I ∞ f :=
  ⟨h.isImmersion, h.isEmbedding⟩

/-- Among smooth embeddings, the Lagrangian condition is precisely the tangent-image condition. -/
@[simp]
theorem isLagrangianEmbedding_iff_of_isSmoothEmbedding
    (hf : Manifold.IsSmoothEmbedding J I ∞ f) :
    hσ.IsLagrangianEmbedding J f ↔ hσ.IsLagrangianMap J f :=
  ⟨fun h ↦ h.isLagrangianMap, fun h ↦ ⟨hf.isImmersion, hf.isEmbedding, h⟩⟩

/-- A Lagrangian embedding is a Lagrangian immersion when the source is nonempty. -/
theorem IsLagrangianEmbedding.isLagrangianImmersion [FiniteDimensional ℝ E] [Nonempty N]
    (h : hσ.IsLagrangianEmbedding J f) : hσ.IsLagrangianImmersion J f :=
  isLagrangianImmersion_iff.mpr ⟨h.isImmersion, h.isLagrangianMap⟩

/-- An isotropic smooth embedding of half the ambient dimension is Lagrangian. -/
theorem IsIsotropicMap.isLagrangianEmbedding_of_finrank [FiniteDimensional ℝ E]
    (h : hσ.IsIsotropicMap J f) (hf : Manifold.IsSmoothEmbedding J I ∞ f)
    (hdim : 2 * finrank ℝ F = finrank ℝ E) : hσ.IsLagrangianEmbedding J f :=
  (isLagrangianEmbedding_iff_of_isSmoothEmbedding hf).mpr
    (h.isLagrangianMap_of_finrank (hf.isImmersion.mfderiv_injective (by simp)) hdim)

/-- On a nonempty source, an embedding is Lagrangian exactly when it is isotropic and has
half the ambient dimension. -/
theorem isLagrangianEmbedding_iff_isIsotropicMap_and_finrank [FiniteDimensional ℝ E]
    [Nonempty N] (hf : Manifold.IsSmoothEmbedding J I ∞ f) :
    hσ.IsLagrangianEmbedding J f ↔
      hσ.IsIsotropicMap J f ∧ 2 * finrank ℝ F = finrank ℝ E := by
  refine ⟨fun h ↦ ⟨h.isLagrangianMap.isIsotropicMap, ?_⟩,
    fun ⟨h, hdim⟩ ↦ h.isLagrangianEmbedding_of_finrank hf hdim⟩
  exact h.isLagrangianMap.two_mul_finrank
    (hf.isImmersion.mfderiv_injective (by simp) (Classical.arbitrary N))

section Reparametrization

variable {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  [IsManifold J ∞ N] [IsManifold J ∞ P]

/-- Reparametrization by a diffeomorphism preserves and reflects Lagrangian embeddings. -/
@[simp]
theorem _root_.Diffeomorph.isLagrangianEmbedding_comp_diffeomorph_iff (φ : P ≃ₘ⟮J, J⟯ N) :
    hσ.IsLagrangianEmbedding J (f ∘ φ) ↔ hσ.IsLagrangianEmbedding J f := by
  constructor
  · intro h
    have hf := (TauCeti.isSmoothEmbedding_comp_diffeomorph_iff φ).mp h.isSmoothEmbedding
    exact ⟨hf.isImmersion, hf.isEmbedding,
      (isLagrangianMap_comp_diffeomorph_iff φ (by simp)).mp h.isLagrangianMap⟩
  · intro h
    exact (isLagrangianEmbedding_iff_of_isSmoothEmbedding
      (TauCeti.isSmoothEmbedding_comp_diffeomorph φ h.isSmoothEmbedding)).mpr
      ((isLagrangianMap_comp_diffeomorph_iff φ (by simp)).mpr h.isLagrangianMap)

end Reparametrization

section Transport

variable {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H M₂] [IsManifold I ∞ M₂]
  {σ₂ : SmoothTwoForm I M₂} {hσ₂ : σ₂.IsNondegenerate}

/-- Symplectomorphisms preserve and reflect Lagrangian embeddings. -/
theorem _root_.Diffeomorph.isLagrangianEmbedding_diffeomorph_comp_iff (ψ : M ≃ₘ⟮I, I⟯ M₂)
    (hψ : SmoothForm.mpullback ψ ψ.contMDiff σ₂ = σ) :
    hσ₂.IsLagrangianEmbedding J (ψ ∘ f) ↔ hσ.IsLagrangianEmbedding J f := by
  constructor
  · intro h
    have hf := (TauCeti.isSmoothEmbedding_diffeomorph_comp_iff ψ).mp h.isSmoothEmbedding
    exact ⟨hf.isImmersion, hf.isEmbedding,
      (isLagrangianMap_diffeomorph_comp_iff ψ hψ).mp h.isLagrangianMap⟩
  · intro h
    exact (isLagrangianEmbedding_iff_of_isSmoothEmbedding
      (TauCeti.isSmoothEmbedding_diffeomorph_comp h.isSmoothEmbedding ψ)).mpr
      ((isLagrangianMap_diffeomorph_comp_iff ψ hψ).mpr h.isLagrangianMap)

end Transport

section Product

variable {E₂ H₂ M₂ F₂ G₂ N₂ : Type*}
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
  {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [IsManifold I₂ ∞ M₂]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [TopologicalSpace G₂]
  {J₂ : ModelWithCorners ℝ F₂ G₂} [TopologicalSpace N₂] [ChartedSpace G₂ N₂]
  [IsManifold J ∞ N] [IsManifold J₂ ∞ N₂]
  {σ₂ : SmoothTwoForm I₂ M₂} {hσ₂ : σ₂.IsNondegenerate} {g : N₂ → M₂}

/-- Products of Lagrangian embeddings are Lagrangian embeddings for the product form. -/
theorem IsLagrangianEmbedding.prodMap (h : hσ.IsLagrangianEmbedding J f)
    (hg : hσ₂.IsLagrangianEmbedding J₂ g) :
    (hσ.prod hσ₂).IsLagrangianEmbedding (J.prod J₂) (Prod.map f g) := by
  apply (isLagrangianEmbedding_iff_of_isSmoothEmbedding
    (h.isSmoothEmbedding.prodMap hg.isSmoothEmbedding)).mpr
  exact h.isLagrangianMap.prodMap hg.isLagrangianMap
    (h.isImmersion.contMDiff.mdifferentiable (by simp))
    (hg.isImmersion.contMDiff.mdifferentiable (by simp))

end Product

section Opens

/-- Restricting a Lagrangian embedding to an open subset of its source gives a Lagrangian
embedding. -/
theorem IsLagrangianEmbedding.comp_subtype_val [IsManifold J ∞ N]
    (h : hσ.IsLagrangianEmbedding J f) (U : Opens N) :
    hσ.IsLagrangianEmbedding J (f ∘ (Subtype.val : U → N)) :=
  (isLagrangianEmbedding_iff_of_isSmoothEmbedding (h.isSmoothEmbedding.comp_subtypeVal U)).2 <|
    h.isLagrangianMap.comp_subtype_val U fun _ _ ↦
      h.isImmersion.contMDiff.mdifferentiableAt (by simp)

/-- A map into an open submanifold is a Lagrangian embedding for the restricted form exactly when
its composition with the inclusion is a Lagrangian embedding. -/
@[simp]
theorem isLagrangianEmbedding_subtype_val_comp_iff {U : Opens M} {g : N → U} :
    hσ.IsLagrangianEmbedding J ((Subtype.val : U → M) ∘ g) ↔
      (hσ.mpullback_subtype_val U).IsLagrangianEmbedding J g := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hg := TauCeti.isSmoothEmbedding_subtypeVal_comp_iff.1 h.isSmoothEmbedding
    exact (isLagrangianEmbedding_iff_of_isSmoothEmbedding hg).2 <|
      (hσ.isLagrangianMap_subtype_val_comp_iff (hg.contMDiff.mdifferentiable (by simp))).1
        h.isLagrangianMap
  · have hg := h.isSmoothEmbedding
    exact (isLagrangianEmbedding_iff_of_isSmoothEmbedding
      (TauCeti.isSmoothEmbedding_subtypeVal_comp_iff.2 hg)).2 <|
      (hσ.isLagrangianMap_subtype_val_comp_iff (hg.contMDiff.mdifferentiable (by simp))).2
        h.isLagrangianMap

end Opens

/-- Nonzero constant rescaling of the form preserves and reflects Lagrangian embeddings. -/
@[simp]
theorem isLagrangianEmbedding_smul_iff (c : ℝ) (hc : c ≠ 0) :
    (hσ.smul c hc).IsLagrangianEmbedding J f ↔ hσ.IsLagrangianEmbedding J f := by
  refine ⟨fun h ↦ ⟨h.isImmersion, h.isEmbedding, ?_⟩, fun h ↦ ⟨h.isImmersion, h.isEmbedding, ?_⟩⟩
  · exact (hσ.isLagrangianMap_smul_iff c hc).1 h.isLagrangianMap
  · exact (hσ.isLagrangianMap_smul_iff c hc).2 h.isLagrangianMap

end TauCeti.SmoothTwoForm.IsNondegenerate
