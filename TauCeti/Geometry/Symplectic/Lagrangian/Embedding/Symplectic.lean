/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Lagrangian.Embedding.Basic

/-!
# Embeddings of symplectic submanifolds

Let `σ` be a fiberwise nondegenerate smooth two-form on `M`. A **symplectic submanifold
embedding** (`TauCeti.SmoothTwoForm.IsNondegenerate.IsSymplecticSubmanifoldEmbedding`) is a smooth
embedding `f : N → M` whose tangent images `df_x(T_x N)` are symplectic subspaces of
`(T_(f x) M, σ_(f x))`, in the sense of `TauCeti.SymplecticForm.IsSymplectic`: they meet their
symplectic complements only in zero. It parametrizes a symplectic embedded submanifold of `M`,
beside the isotropic, coisotropic and Lagrangian embeddings.

Equivalently, a smooth embedding is a symplectic submanifold embedding exactly when it pulls `σ`
back to a nondegenerate form
(`isSymplecticSubmanifoldEmbedding_iff_isNondegenerate_mpullback`),
so that `f` is a symplectic embedding, in the usual sense of a map pulling one symplectic form back
to another, of `(N, f*σ)` into `(M, σ)`. The name records that the form on `N` is not given but
induced. When `σ` is symplectic so is `f*σ`, and in finite dimension a nonempty source then has
even dimension.

As for the other tangent-image embeddings, the notion is independent of the parametrization,
transported by symplectomorphisms, preserved by products, by restriction of the source to an open
subset and by nonzero rescaling of `σ`, and a map into an open submanifold is a symplectic
submanifold embedding for the restricted form exactly when its composition with the inclusion is
one.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Sections 2.1 and 3.4.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 1 and 3.
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
/-- A symplectic submanifold embedding is a smooth immersion, a topological embedding, and a map
with symplectic tangent images. It parametrizes a symplectic embedded submanifold. -/
structure IsSymplecticSubmanifoldEmbedding (f : N → M) : Prop where
  /-- The parametrization is a smooth immersion. -/
  isImmersion : Manifold.IsImmersion J I ∞ f
  /-- The parametrization is a homeomorphism onto its image. -/
  isEmbedding : Topology.IsEmbedding f
  /-- Every tangent image is a symplectic subspace. -/
  hasSymplecticTangentImages : hσ.HasSymplecticTangentImages J f

/-- A symplectic submanifold embedding is a smooth embedding in Mathlib's sense. -/
theorem IsSymplecticSubmanifoldEmbedding.isSmoothEmbedding
    (h : hσ.IsSymplecticSubmanifoldEmbedding J f) : Manifold.IsSmoothEmbedding J I ∞ f :=
  ⟨h.isImmersion, h.isEmbedding⟩

/-- Among smooth embeddings, the symplectic submanifold condition is precisely the tangent-image
condition. -/
@[simp]
theorem isSymplecticSubmanifoldEmbedding_iff_of_isSmoothEmbedding
    (hf : Manifold.IsSmoothEmbedding J I ∞ f) :
    hσ.IsSymplecticSubmanifoldEmbedding J f ↔ hσ.HasSymplecticTangentImages J f :=
  ⟨fun h ↦ h.hasSymplecticTangentImages, fun h ↦ ⟨hf.isImmersion, hf.isEmbedding, h⟩⟩

/-! ### The induced form -/

section Pullback

variable [IsManifold J ∞ N]

/-- A smooth embedding is a symplectic submanifold embedding exactly when it pulls `σ` back to a
nondegenerate form. -/
theorem isSymplecticSubmanifoldEmbedding_iff_isNondegenerate_mpullback
    (hf : Manifold.IsSmoothEmbedding J I ∞ f) :
    hσ.IsSymplecticSubmanifoldEmbedding J f ↔
      SmoothTwoForm.IsNondegenerate (SmoothForm.mpullback f hf.contMDiff σ) := by
  rw [isSymplecticSubmanifoldEmbedding_iff_of_isSmoothEmbedding hf,
    isNondegenerate_mpullback_iff hf.contMDiff]
  exact (and_iff_left (hf.isImmersion.mfderiv_injective (by simp))).symm

/-- A symplectic submanifold embedding pulls `σ` back to a nondegenerate form. -/
theorem IsSymplecticSubmanifoldEmbedding.isNondegenerate_mpullback
    (h : hσ.IsSymplecticSubmanifoldEmbedding J f) :
    SmoothTwoForm.IsNondegenerate (SmoothForm.mpullback f h.isSmoothEmbedding.contMDiff σ) :=
  (isSymplecticSubmanifoldEmbedding_iff_isNondegenerate_mpullback h.isSmoothEmbedding).1 h

/-- A symplectic submanifold embedding pulls a symplectic form back to a symplectic form. -/
theorem IsSymplecticSubmanifoldEmbedding.isSymplectic_mpullback
    (h : hσ.IsSymplecticSubmanifoldEmbedding J f) (hσs : σ.IsSymplectic) :
    SmoothTwoForm.IsSymplectic (SmoothForm.mpullback f h.isSmoothEmbedding.contMDiff σ) :=
  h.hasSymplecticTangentImages.isSymplectic_mpullback hσs h.isSmoothEmbedding.contMDiff
    (h.isImmersion.mfderiv_injective (by simp))

end Pullback

/-- A symplectic submanifold embedding of a nonempty finite-dimensional manifold comes from an
even-dimensional manifold. -/
theorem IsSymplecticSubmanifoldEmbedding.even_finrank [FiniteDimensional ℝ F] [Nonempty N]
    (h : hσ.IsSymplecticSubmanifoldEmbedding J f) : Even (finrank ℝ F) :=
  h.hasSymplecticTangentImages.even_finrank
    (h.isImmersion.mfderiv_injective (by simp) (Classical.arbitrary N))

/-! ### Reparametrization and transport -/

section Reparametrization

variable {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  [IsManifold J ∞ N] [IsManifold J ∞ P]

/-- Reparametrization by a diffeomorphism preserves and reflects symplectic submanifold
embeddings. -/
@[simp]
theorem _root_.Diffeomorph.isSymplecticSubmanifoldEmbedding_comp_diffeomorph_iff
    (φ : P ≃ₘ⟮J, J⟯ N) :
    hσ.IsSymplecticSubmanifoldEmbedding J (f ∘ φ) ↔ hσ.IsSymplecticSubmanifoldEmbedding J f := by
  constructor
  · intro h
    have hf := (TauCeti.isSmoothEmbedding_comp_diffeomorph_iff φ).mp h.isSmoothEmbedding
    exact (isSymplecticSubmanifoldEmbedding_iff_of_isSmoothEmbedding hf).2
      ((hasSymplecticTangentImages_comp_diffeomorph_iff φ (by simp)).mp
        h.hasSymplecticTangentImages)
  · intro h
    exact (isSymplecticSubmanifoldEmbedding_iff_of_isSmoothEmbedding
      (TauCeti.isSmoothEmbedding_comp_diffeomorph φ h.isSmoothEmbedding)).2
      ((hasSymplecticTangentImages_comp_diffeomorph_iff φ (by simp)).mpr
        h.hasSymplecticTangentImages)

end Reparametrization

section Transport

variable {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H M₂] [IsManifold I ∞ M₂]
  {σ₂ : SmoothTwoForm I M₂} {hσ₂ : σ₂.IsNondegenerate}

/-- Symplectomorphisms preserve and reflect symplectic submanifold embeddings. -/
theorem _root_.Diffeomorph.isSymplecticSubmanifoldEmbedding_diffeomorph_comp_iff
    (ψ : M ≃ₘ⟮I, I⟯ M₂) (hψ : SmoothForm.mpullback ψ ψ.contMDiff σ₂ = σ) :
    hσ₂.IsSymplecticSubmanifoldEmbedding J (ψ ∘ f) ↔
      hσ.IsSymplecticSubmanifoldEmbedding J f := by
  constructor
  · intro h
    have hf := (TauCeti.isSmoothEmbedding_diffeomorph_comp_iff ψ).mp h.isSmoothEmbedding
    exact (isSymplecticSubmanifoldEmbedding_iff_of_isSmoothEmbedding hf).2
      ((hasSymplecticTangentImages_diffeomorph_comp_iff ψ hψ).mp h.hasSymplecticTangentImages)
  · intro h
    exact (isSymplecticSubmanifoldEmbedding_iff_of_isSmoothEmbedding
      (TauCeti.isSmoothEmbedding_diffeomorph_comp h.isSmoothEmbedding ψ)).2
      ((hasSymplecticTangentImages_diffeomorph_comp_iff ψ hψ).mpr h.hasSymplecticTangentImages)

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

/-- Products of symplectic submanifold embeddings are symplectic submanifold embeddings for the
product form. -/
theorem IsSymplecticSubmanifoldEmbedding.prodMap (h : hσ.IsSymplecticSubmanifoldEmbedding J f)
    (hg : hσ₂.IsSymplecticSubmanifoldEmbedding J₂ g) :
    (hσ.prod hσ₂).IsSymplecticSubmanifoldEmbedding (J.prod J₂) (Prod.map f g) :=
  (isSymplecticSubmanifoldEmbedding_iff_of_isSmoothEmbedding
    (h.isSmoothEmbedding.prodMap hg.isSmoothEmbedding)).2 <|
    h.hasSymplecticTangentImages.prodMap hg.hasSymplecticTangentImages
      (h.isImmersion.contMDiff.mdifferentiable (by simp))
      (hg.isImmersion.contMDiff.mdifferentiable (by simp))

end Product

/-! ### Open submanifolds -/

section Opens

/-- Restricting a symplectic submanifold embedding to an open subset of its source gives a
symplectic submanifold embedding. -/
theorem IsSymplecticSubmanifoldEmbedding.comp_subtype_val [IsManifold J ∞ N]
    (h : hσ.IsSymplecticSubmanifoldEmbedding J f) (U : Opens N) :
    hσ.IsSymplecticSubmanifoldEmbedding J (f ∘ (Subtype.val : U → N)) :=
  (isSymplecticSubmanifoldEmbedding_iff_of_isSmoothEmbedding
    (h.isSmoothEmbedding.comp_subtypeVal U)).2 <|
    h.hasSymplecticTangentImages.comp_subtype_val U fun _ _ ↦
      h.isImmersion.contMDiff.mdifferentiableAt (by simp)

/-- A map into an open submanifold is a symplectic submanifold embedding for the restricted form
exactly when its composition with the inclusion is a symplectic submanifold embedding. -/
@[simp]
theorem isSymplecticSubmanifoldEmbedding_subtype_val_comp_iff {U : Opens M} {g : N → U} :
    hσ.IsSymplecticSubmanifoldEmbedding J ((Subtype.val : U → M) ∘ g) ↔
      (hσ.mpullback_subtype_val U).IsSymplecticSubmanifoldEmbedding J g := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hg := TauCeti.isSmoothEmbedding_subtypeVal_comp_iff.1 h.isSmoothEmbedding
    exact (isSymplecticSubmanifoldEmbedding_iff_of_isSmoothEmbedding hg).2 <|
      (hσ.hasSymplecticTangentImages_subtype_val_comp_iff
        (hg.contMDiff.mdifferentiable (by simp))).1 h.hasSymplecticTangentImages
  · have hg := h.isSmoothEmbedding
    exact (isSymplecticSubmanifoldEmbedding_iff_of_isSmoothEmbedding
      (TauCeti.isSmoothEmbedding_subtypeVal_comp_iff.2 hg)).2 <|
      (hσ.hasSymplecticTangentImages_subtype_val_comp_iff
        (hg.contMDiff.mdifferentiable (by simp))).2 h.hasSymplecticTangentImages

end Opens

/-! ### Rescaling -/

/-- Nonzero constant rescaling of the form preserves and reflects symplectic submanifold
embeddings. -/
@[simp]
theorem isSymplecticSubmanifoldEmbedding_smul_iff (c : ℝ) (hc : c ≠ 0) :
    (hσ.smul c hc).IsSymplecticSubmanifoldEmbedding J f ↔
      hσ.IsSymplecticSubmanifoldEmbedding J f := by
  refine ⟨fun h ↦ ⟨h.isImmersion, h.isEmbedding, ?_⟩, fun h ↦ ⟨h.isImmersion, h.isEmbedding, ?_⟩⟩
  · exact (hσ.hasSymplecticTangentImages_smul_iff c hc).1 h.hasSymplecticTangentImages
  · exact (hσ.hasSymplecticTangentImages_smul_iff c hc).2 h.hasSymplecticTangentImages

end TauCeti.SmoothTwoForm.IsNondegenerate
