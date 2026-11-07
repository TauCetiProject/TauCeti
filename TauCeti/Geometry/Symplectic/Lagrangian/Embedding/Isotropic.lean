/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Basic

/-!
# Isotropic and coisotropic embeddings

Let `σ` be a fiberwise nondegenerate smooth two-form on `M`. An **isotropic embedding**
(`TauCeti.SmoothTwoForm.IsNondegenerate.IsIsotropicEmbedding`) is a smooth embedding `f : N → M`
whose tangent images `df_x(T_x N)` are isotropic subspaces of `(T_(f x) M, σ_(f x))`, and a
**coisotropic embedding** (`TauCeti.SmoothTwoForm.IsNondegenerate.IsCoisotropicEmbedding`) is one
whose tangent images are coisotropic. They parametrize the isotropic and coisotropic embedded
submanifolds of `M`, beside the Lagrangian embeddings of
`TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Basic`: an embedding is Lagrangian exactly when
it is both isotropic and coisotropic. Unlike an isotropic or coisotropic map, such an embedding is a
homeomorphism onto its image, so its image has no self-intersections.

The tangent-image conditions are the existing map predicates
`TauCeti.SmoothTwoForm.IsNondegenerate.IsIsotropicMap` and `IsCoisotropicMap`, so the API here
specializes theirs to embeddings:

* in finite dimension, a nonempty isotropic embedding has `2 dim N ≤ dim M` and a nonempty
  coisotropic embedding has `dim M ≤ 2 dim N`; an isotropic embedding with `2 dim N = dim M` is
  Lagrangian;
* both notions are independent of the parametrization, transported by symplectomorphisms and
  preserved by products;
* restricting the source to an open subset preserves them, and a map into an open submanifold is
  an isotropic or coisotropic embedding for the restricted form exactly when its composition with
  the inclusion is one;
* nonzero constant rescaling of `σ` preserves and reflects them.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 3 and 7.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.4.
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
/-- An isotropic embedding is a smooth immersion, a topological embedding, and a map with isotropic
tangent images. It parametrizes an isotropic embedded submanifold. -/
structure IsIsotropicEmbedding (f : N → M) : Prop where
  /-- The parametrization is a smooth immersion. -/
  isImmersion : Manifold.IsImmersion J I ∞ f
  /-- The parametrization is a homeomorphism onto its image. -/
  isEmbedding : Topology.IsEmbedding f
  /-- Every tangent image is an isotropic subspace. -/
  isIsotropicMap : hσ.IsIsotropicMap J f

variable (hσ J) in
/-- A coisotropic embedding is a smooth immersion, a topological embedding, and a map with
coisotropic tangent images. It parametrizes a coisotropic embedded submanifold. -/
structure IsCoisotropicEmbedding (f : N → M) : Prop where
  /-- The parametrization is a smooth immersion. -/
  isImmersion : Manifold.IsImmersion J I ∞ f
  /-- The parametrization is a homeomorphism onto its image. -/
  isEmbedding : Topology.IsEmbedding f
  /-- Every tangent image is a coisotropic subspace. -/
  isCoisotropicMap : hσ.IsCoisotropicMap J f

/-- An isotropic embedding is a smooth embedding in Mathlib's sense. -/
theorem IsIsotropicEmbedding.isSmoothEmbedding (h : hσ.IsIsotropicEmbedding J f) :
    Manifold.IsSmoothEmbedding J I ∞ f :=
  ⟨h.isImmersion, h.isEmbedding⟩

/-- A coisotropic embedding is a smooth embedding in Mathlib's sense. -/
theorem IsCoisotropicEmbedding.isSmoothEmbedding (h : hσ.IsCoisotropicEmbedding J f) :
    Manifold.IsSmoothEmbedding J I ∞ f :=
  ⟨h.isImmersion, h.isEmbedding⟩

/-- Among smooth embeddings, the isotropic condition is precisely the tangent-image condition. -/
@[simp]
theorem isIsotropicEmbedding_iff_of_isSmoothEmbedding
    (hf : Manifold.IsSmoothEmbedding J I ∞ f) :
    hσ.IsIsotropicEmbedding J f ↔ hσ.IsIsotropicMap J f :=
  ⟨fun h ↦ h.isIsotropicMap, fun h ↦ ⟨hf.isImmersion, hf.isEmbedding, h⟩⟩

/-- Among smooth embeddings, the coisotropic condition is precisely the tangent-image condition. -/
@[simp]
theorem isCoisotropicEmbedding_iff_of_isSmoothEmbedding
    (hf : Manifold.IsSmoothEmbedding J I ∞ f) :
    hσ.IsCoisotropicEmbedding J f ↔ hσ.IsCoisotropicMap J f :=
  ⟨fun h ↦ h.isCoisotropicMap, fun h ↦ ⟨hf.isImmersion, hf.isEmbedding, h⟩⟩

/-! ### Lagrangian embeddings -/

/-- A Lagrangian embedding is an isotropic embedding. -/
theorem IsLagrangianEmbedding.isIsotropicEmbedding (h : hσ.IsLagrangianEmbedding J f) :
    hσ.IsIsotropicEmbedding J f :=
  ⟨h.isImmersion, h.isEmbedding, h.isLagrangianMap.isIsotropicMap⟩

/-- A Lagrangian embedding is a coisotropic embedding. -/
theorem IsLagrangianEmbedding.isCoisotropicEmbedding (h : hσ.IsLagrangianEmbedding J f) :
    hσ.IsCoisotropicEmbedding J f :=
  ⟨h.isImmersion, h.isEmbedding, h.isLagrangianMap.isCoisotropicMap⟩

/-- An embedding is Lagrangian exactly when it is both isotropic and coisotropic. -/
theorem isLagrangianEmbedding_iff_isIsotropicEmbedding_and_isCoisotropicEmbedding :
    hσ.IsLagrangianEmbedding J f ↔ hσ.IsIsotropicEmbedding J f ∧ hσ.IsCoisotropicEmbedding J f :=
  ⟨fun h ↦ ⟨h.isIsotropicEmbedding, h.isCoisotropicEmbedding⟩, fun ⟨hi, hc⟩ ↦
    ⟨hi.isImmersion, hi.isEmbedding,
      isLagrangianMap_iff.2 ⟨hi.isIsotropicMap, hc.isCoisotropicMap⟩⟩⟩

/-! ### Dimension counts -/

section Dimension

variable [FiniteDimensional ℝ E]

/-- An isotropic embedding of a nonempty manifold has at most half the ambient dimension:
`2 dim N ≤ dim M`. -/
theorem IsIsotropicEmbedding.two_mul_finrank_le [Nonempty N] (h : hσ.IsIsotropicEmbedding J f) :
    2 * finrank ℝ F ≤ finrank ℝ E :=
  h.isIsotropicMap.two_mul_finrank_le
    (h.isImmersion.mfderiv_injective (by simp) (Classical.arbitrary N))

/-- A coisotropic embedding of a nonempty finite-dimensional manifold has at least half the
ambient dimension: `dim M ≤ 2 dim N`. -/
theorem IsCoisotropicEmbedding.finrank_le_two_mul_finrank [FiniteDimensional ℝ F] [Nonempty N]
    (h : hσ.IsCoisotropicEmbedding J f) : finrank ℝ E ≤ 2 * finrank ℝ F :=
  h.isCoisotropicMap.finrank_le_two_mul_finrank (Classical.arbitrary N)

/-- An isotropic embedding of half the ambient dimension is a Lagrangian embedding. -/
theorem IsIsotropicEmbedding.isLagrangianEmbedding_of_finrank (h : hσ.IsIsotropicEmbedding J f)
    (hdim : 2 * finrank ℝ F = finrank ℝ E) : hσ.IsLagrangianEmbedding J f :=
  h.isIsotropicMap.isLagrangianEmbedding_of_finrank h.isSmoothEmbedding hdim

end Dimension

/-! ### Reparametrization and transport -/

section Reparametrization

variable {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  [IsManifold J ∞ N] [IsManifold J ∞ P]

/-- Reparametrization by a diffeomorphism preserves and reflects isotropic embeddings. -/
@[simp]
theorem _root_.Diffeomorph.isIsotropicEmbedding_comp_diffeomorph_iff (φ : P ≃ₘ⟮J, J⟯ N) :
    hσ.IsIsotropicEmbedding J (f ∘ φ) ↔ hσ.IsIsotropicEmbedding J f := by
  constructor
  · intro h
    have hf := (TauCeti.isSmoothEmbedding_comp_diffeomorph_iff φ).mp h.isSmoothEmbedding
    exact (isIsotropicEmbedding_iff_of_isSmoothEmbedding hf).2
      ((isIsotropicMap_comp_diffeomorph_iff φ (by simp)).mp h.isIsotropicMap)
  · intro h
    exact (isIsotropicEmbedding_iff_of_isSmoothEmbedding
      (TauCeti.isSmoothEmbedding_comp_diffeomorph φ h.isSmoothEmbedding)).2
      ((isIsotropicMap_comp_diffeomorph_iff φ (by simp)).mpr h.isIsotropicMap)

/-- Reparametrization by a diffeomorphism preserves and reflects coisotropic embeddings. -/
@[simp]
theorem _root_.Diffeomorph.isCoisotropicEmbedding_comp_diffeomorph_iff (φ : P ≃ₘ⟮J, J⟯ N) :
    hσ.IsCoisotropicEmbedding J (f ∘ φ) ↔ hσ.IsCoisotropicEmbedding J f := by
  constructor
  · intro h
    have hf := (TauCeti.isSmoothEmbedding_comp_diffeomorph_iff φ).mp h.isSmoothEmbedding
    exact (isCoisotropicEmbedding_iff_of_isSmoothEmbedding hf).2
      ((isCoisotropicMap_comp_diffeomorph_iff φ (by simp)).mp h.isCoisotropicMap)
  · intro h
    exact (isCoisotropicEmbedding_iff_of_isSmoothEmbedding
      (TauCeti.isSmoothEmbedding_comp_diffeomorph φ h.isSmoothEmbedding)).2
      ((isCoisotropicMap_comp_diffeomorph_iff φ (by simp)).mpr h.isCoisotropicMap)

end Reparametrization

section Transport

variable {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H M₂] [IsManifold I ∞ M₂]
  {σ₂ : SmoothTwoForm I M₂} {hσ₂ : σ₂.IsNondegenerate}

/-- Symplectomorphisms preserve and reflect isotropic embeddings. -/
theorem _root_.Diffeomorph.isIsotropicEmbedding_diffeomorph_comp_iff (ψ : M ≃ₘ⟮I, I⟯ M₂)
    (hψ : SmoothForm.mpullback ψ ψ.contMDiff σ₂ = σ) :
    hσ₂.IsIsotropicEmbedding J (ψ ∘ f) ↔ hσ.IsIsotropicEmbedding J f := by
  constructor
  · intro h
    have hf := (TauCeti.isSmoothEmbedding_diffeomorph_comp_iff ψ).mp h.isSmoothEmbedding
    exact (isIsotropicEmbedding_iff_of_isSmoothEmbedding hf).2
      ((isIsotropicMap_diffeomorph_comp_iff ψ hψ).mp h.isIsotropicMap)
  · intro h
    exact (isIsotropicEmbedding_iff_of_isSmoothEmbedding
      (TauCeti.isSmoothEmbedding_diffeomorph_comp h.isSmoothEmbedding ψ)).2
      ((isIsotropicMap_diffeomorph_comp_iff ψ hψ).mpr h.isIsotropicMap)

/-- Symplectomorphisms preserve and reflect coisotropic embeddings. -/
theorem _root_.Diffeomorph.isCoisotropicEmbedding_diffeomorph_comp_iff (ψ : M ≃ₘ⟮I, I⟯ M₂)
    (hψ : SmoothForm.mpullback ψ ψ.contMDiff σ₂ = σ) :
    hσ₂.IsCoisotropicEmbedding J (ψ ∘ f) ↔ hσ.IsCoisotropicEmbedding J f := by
  constructor
  · intro h
    have hf := (TauCeti.isSmoothEmbedding_diffeomorph_comp_iff ψ).mp h.isSmoothEmbedding
    exact (isCoisotropicEmbedding_iff_of_isSmoothEmbedding hf).2
      ((isCoisotropicMap_diffeomorph_comp_iff ψ hψ).mp h.isCoisotropicMap)
  · intro h
    exact (isCoisotropicEmbedding_iff_of_isSmoothEmbedding
      (TauCeti.isSmoothEmbedding_diffeomorph_comp h.isSmoothEmbedding ψ)).2
      ((isCoisotropicMap_diffeomorph_comp_iff ψ hψ).mpr h.isCoisotropicMap)

end Transport

/-! ### Products -/

section Product

variable {E₂ H₂ M₂ F₂ G₂ N₂ : Type*}
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
  {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [IsManifold I₂ ∞ M₂]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [TopologicalSpace G₂]
  {J₂ : ModelWithCorners ℝ F₂ G₂} [TopologicalSpace N₂] [ChartedSpace G₂ N₂]
  [IsManifold J ∞ N] [IsManifold J₂ ∞ N₂]
  {σ₂ : SmoothTwoForm I₂ M₂} {hσ₂ : σ₂.IsNondegenerate} {g : N₂ → M₂}

/-- Products of isotropic embeddings are isotropic embeddings for the product form. -/
theorem IsIsotropicEmbedding.prodMap (h : hσ.IsIsotropicEmbedding J f)
    (hg : hσ₂.IsIsotropicEmbedding J₂ g) :
    (hσ.prod hσ₂).IsIsotropicEmbedding (J.prod J₂) (Prod.map f g) :=
  (isIsotropicEmbedding_iff_of_isSmoothEmbedding
    (h.isSmoothEmbedding.prodMap hg.isSmoothEmbedding)).2 <|
    h.isIsotropicMap.prodMap hg.isIsotropicMap
      (h.isImmersion.contMDiff.mdifferentiable (by simp))
      (hg.isImmersion.contMDiff.mdifferentiable (by simp))

/-- Products of coisotropic embeddings are coisotropic embeddings for the product form. -/
theorem IsCoisotropicEmbedding.prodMap (h : hσ.IsCoisotropicEmbedding J f)
    (hg : hσ₂.IsCoisotropicEmbedding J₂ g) :
    (hσ.prod hσ₂).IsCoisotropicEmbedding (J.prod J₂) (Prod.map f g) :=
  (isCoisotropicEmbedding_iff_of_isSmoothEmbedding
    (h.isSmoothEmbedding.prodMap hg.isSmoothEmbedding)).2 <|
    h.isCoisotropicMap.prodMap hg.isCoisotropicMap
      (h.isImmersion.contMDiff.mdifferentiable (by simp))
      (hg.isImmersion.contMDiff.mdifferentiable (by simp))

end Product

/-! ### Open submanifolds -/

section Opens

/-- Restricting an isotropic embedding to an open subset of its source gives an isotropic
embedding. -/
theorem IsIsotropicEmbedding.comp_subtype_val [IsManifold J ∞ N]
    (h : hσ.IsIsotropicEmbedding J f) (U : Opens N) :
    hσ.IsIsotropicEmbedding J (f ∘ (Subtype.val : U → N)) :=
  (isIsotropicEmbedding_iff_of_isSmoothEmbedding (h.isSmoothEmbedding.comp_subtypeVal U)).2 <|
    h.isIsotropicMap.comp_subtype_val U fun _ _ ↦
      h.isImmersion.contMDiff.mdifferentiableAt (by simp)

/-- Restricting a coisotropic embedding to an open subset of its source gives a coisotropic
embedding. -/
theorem IsCoisotropicEmbedding.comp_subtype_val [IsManifold J ∞ N]
    (h : hσ.IsCoisotropicEmbedding J f) (U : Opens N) :
    hσ.IsCoisotropicEmbedding J (f ∘ (Subtype.val : U → N)) :=
  (isCoisotropicEmbedding_iff_of_isSmoothEmbedding (h.isSmoothEmbedding.comp_subtypeVal U)).2 <|
    h.isCoisotropicMap.comp_subtype_val U fun _ _ ↦
      h.isImmersion.contMDiff.mdifferentiableAt (by simp)

variable {U : Opens M} {g : N → U}

/-- A map into an open submanifold is an isotropic embedding for the restricted form exactly when
its composition with the inclusion is an isotropic embedding. -/
@[simp]
theorem isIsotropicEmbedding_subtype_val_comp_iff :
    hσ.IsIsotropicEmbedding J ((Subtype.val : U → M) ∘ g) ↔
      (hσ.mpullback_subtype_val U).IsIsotropicEmbedding J g := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hg := TauCeti.isSmoothEmbedding_subtypeVal_comp_iff.1 h.isSmoothEmbedding
    exact (isIsotropicEmbedding_iff_of_isSmoothEmbedding hg).2 <|
      (hσ.isIsotropicMap_subtype_val_comp_iff (hg.contMDiff.mdifferentiable (by simp))).1
        h.isIsotropicMap
  · have hg := h.isSmoothEmbedding
    exact (isIsotropicEmbedding_iff_of_isSmoothEmbedding
      (TauCeti.isSmoothEmbedding_subtypeVal_comp_iff.2 hg)).2 <|
      (hσ.isIsotropicMap_subtype_val_comp_iff (hg.contMDiff.mdifferentiable (by simp))).2
        h.isIsotropicMap

/-- A map into an open submanifold is a coisotropic embedding for the restricted form exactly when
its composition with the inclusion is a coisotropic embedding. -/
@[simp]
theorem isCoisotropicEmbedding_subtype_val_comp_iff :
    hσ.IsCoisotropicEmbedding J ((Subtype.val : U → M) ∘ g) ↔
      (hσ.mpullback_subtype_val U).IsCoisotropicEmbedding J g := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hg := TauCeti.isSmoothEmbedding_subtypeVal_comp_iff.1 h.isSmoothEmbedding
    exact (isCoisotropicEmbedding_iff_of_isSmoothEmbedding hg).2 <|
      (hσ.isCoisotropicMap_subtype_val_comp_iff (hg.contMDiff.mdifferentiable (by simp))).1
        h.isCoisotropicMap
  · have hg := h.isSmoothEmbedding
    exact (isCoisotropicEmbedding_iff_of_isSmoothEmbedding
      (TauCeti.isSmoothEmbedding_subtypeVal_comp_iff.2 hg)).2 <|
      (hσ.isCoisotropicMap_subtype_val_comp_iff (hg.contMDiff.mdifferentiable (by simp))).2
        h.isCoisotropicMap

end Opens

/-! ### Rescaling -/

/-- Nonzero constant rescaling of the form preserves and reflects isotropic embeddings. -/
@[simp]
theorem isIsotropicEmbedding_smul_iff (c : ℝ) (hc : c ≠ 0) :
    (hσ.smul c hc).IsIsotropicEmbedding J f ↔ hσ.IsIsotropicEmbedding J f := by
  refine ⟨fun h ↦ ⟨h.isImmersion, h.isEmbedding, ?_⟩, fun h ↦ ⟨h.isImmersion, h.isEmbedding, ?_⟩⟩
  · exact (hσ.isIsotropicMap_smul_iff c hc).1 h.isIsotropicMap
  · exact (hσ.isIsotropicMap_smul_iff c hc).2 h.isIsotropicMap

/-- Nonzero constant rescaling of the form preserves and reflects coisotropic embeddings. -/
@[simp]
theorem isCoisotropicEmbedding_smul_iff (c : ℝ) (hc : c ≠ 0) :
    (hσ.smul c hc).IsCoisotropicEmbedding J f ↔ hσ.IsCoisotropicEmbedding J f := by
  refine ⟨fun h ↦ ⟨h.isImmersion, h.isEmbedding, ?_⟩, fun h ↦ ⟨h.isImmersion, h.isEmbedding, ?_⟩⟩
  · exact (hσ.isCoisotropicMap_smul_iff c hc).1 h.isCoisotropicMap
  · exact (hσ.isCoisotropicMap_smul_iff c hc).2 h.isCoisotropicMap

end TauCeti.SmoothTwoForm.IsNondegenerate
