/-
Copyright (c) 2026 The Tau Ceti contributors and Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Jon Crall, GPT 5.6 High, OpenAI GPT-6
-/
module

public import Mathlib.Analysis.InnerProductSpace.Semisimple
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Reducing subspaces of inner-product spaces

A subspace reduces an endomorphism when both it and its orthogonal complement are invariant.
For a symmetric endomorphism, invariance of the subspace alone is enough. When an orthogonal
projection exists, reduction is equivalently commutation with that projection; in particular the
orthogonal projection onto a subspace invariant under a symmetric endomorphism commutes with it.

For a bounded operator `A` on a Hilbert space and a complete subspace invariant under both `A`
and its adjoint, the adjoint of the restriction of `A` is the restriction of the adjoint
(`ContinuousLinearMap.adjoint_restrict`), so the restriction of a normal operator is normal
(`IsStarNormal.restrict`).
-/

public section

open Module End

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A subspace is reducing for an endomorphism when both it and its orthogonal complement are
invariant under the endomorphism. -/
def IsReducing (U : Submodule 𝕜 E) (A : Module.End 𝕜 E) : Prop :=
  U ∈ A.invtSubmodule ∧ Uᗮ ∈ A.invtSubmodule

/-- A subspace is reducing exactly when it and its orthogonal complement are invariant. -/
theorem isReducing_iff (U : Submodule 𝕜 E) (A : Module.End 𝕜 E) :
    U.IsReducing A ↔ U ∈ A.invtSubmodule ∧ Uᗮ ∈ A.invtSubmodule :=
  Iff.rfl

/-- A reducing subspace is invariant under the endomorphism. -/
theorem IsReducing.mem_invtSubmodule {U : Submodule 𝕜 E} {A : Module.End 𝕜 E}
    (hU : U.IsReducing A) : U ∈ A.invtSubmodule :=
  hU.1

/-- The orthogonal complement of a reducing subspace is invariant under the endomorphism. -/
theorem IsReducing.orthogonal_mem_invtSubmodule {U : Submodule 𝕜 E} {A : Module.End 𝕜 E}
    (hU : U.IsReducing A) : Uᗮ ∈ A.invtSubmodule :=
  hU.2

/-- The orthogonal complement reduces an endomorphism exactly when the original subspace does. -/
@[simp]
theorem isReducing_orthogonal_iff (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : Module.End 𝕜 E) : Uᗮ.IsReducing A ↔ U.IsReducing A := by
  rw [isReducing_iff, isReducing_iff, orthogonal_orthogonal]
  exact and_comm

/-- A subspace reduces a symmetric endomorphism exactly when it is invariant. -/
theorem _root_.LinearMap.IsSymmetric.isReducing_iff_mem_invtSubmodule {A : Module.End 𝕜 E}
    (hA : A.IsSymmetric) (U : Submodule 𝕜 E) :
    U.IsReducing A ↔ U ∈ A.invtSubmodule :=
  ⟨IsReducing.mem_invtSubmodule, fun hU ↦
    ⟨hU, hA.orthogonalComplement_mem_invtSubmodule hU⟩⟩

/-- A subspace admitting an orthogonal projection reduces an endomorphism exactly when its
orthogonal projection commutes with that endomorphism. -/
theorem isReducing_iff_commute_starProjection (U : Submodule 𝕜 E) [U.HasOrthogonalProjection]
    (A : Module.End 𝕜 E) :
    U.IsReducing A ↔ Commute U.starProjection.toLinearMap A := by
  rw [isReducing_iff]
  simpa only [range_starProjection, ker_starProjection] using
    (LinearMap.IsIdempotentElem.commute_iff
    (ContinuousLinearMap.IsIdempotentElem.toLinearMap U.isIdempotentElem_starProjection)
    (T := A)).symm

/-- The orthogonal projection onto a subspace invariant under a symmetric endomorphism commutes
with that endomorphism. -/
theorem _root_.LinearMap.IsSymmetric.starProjection_apply_comm {A : Module.End 𝕜 E}
    (hA : A.IsSymmetric) {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : U ∈ A.invtSubmodule) (x : E) : U.starProjection (A x) = A (U.starProjection x) := by
  have h := (U.isReducing_iff_commute_starProjection A).mp
    ((hA.isReducing_iff_mem_invtSubmodule U).mpr hU)
  simpa only [_root_.mul_apply_eq_comp, ContinuousLinearMap.coe_coe] using congr($(h.eq) x)


variable {U V : Submodule 𝕜 E} {A : End 𝕜 E}

/-- The zero subspace reduces every endomorphism. -/
@[simp]
theorem isReducing_bot : (⊥ : Submodule 𝕜 E).IsReducing A :=
  ⟨invtSubmodule.bot_mem A, by simp⟩

/-- The whole space reduces every endomorphism. -/
@[simp]
theorem isReducing_top : (⊤ : Submodule 𝕜 E).IsReducing A :=
  ⟨invtSubmodule.top_mem A, by simp⟩

/-- The supremum of a family of reducing subspaces is reducing. -/
theorem IsReducing.iSup {ι : Type*} {U : ι → Submodule 𝕜 E} (hU : ∀ i, (U i).IsReducing A) :
    (⨆ i, U i).IsReducing A := by
  refine ⟨(mem_invtSubmodule_iff_map_le A).mpr ?_, ?_⟩
  · rw [map_iSup]
    exact iSup_mono fun i ↦ (mem_invtSubmodule_iff_map_le A).mp (hU i).1
  · rw [← iInf_orthogonal, End.mem_invtSubmodule, comap_iInf]
    exact iInf_mono fun i ↦ (hU i).2

/-- The span of two reducing subspaces is reducing. -/
theorem IsReducing.sup (hU : U.IsReducing A) (hV : V.IsReducing A) : (U ⊔ V).IsReducing A := by
  rw [sup_eq_iSup]
  exact IsReducing.iSup (Bool.forall_bool.mpr ⟨hV, hU⟩)


end Submodule

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {U : Submodule 𝕜 E}

/-- A subspace with an orthogonal projection reduces a bounded operator `A` exactly when `A`
commutes with the orthogonal projection onto it. -/
theorem isReducing_coe_iff_commute_starProjection [U.HasOrthogonalProjection] {A : E →L[𝕜] E} :
    U.IsReducing A ↔ Commute U.starProjection A := by
  rw [ContinuousLinearMap.IsIdempotentElem.commute_iff (isIdempotentElem_starProjection U),
    isReducing_iff, range_starProjection, ker_starProjection]

end Submodule

open Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {U : Submodule 𝕜 E}

/-- A subspace with an orthogonal projection reduces a bounded operator `A` on a Hilbert space
exactly when it is invariant under both `A` and its adjoint. -/
theorem ContinuousLinearMap.isReducing_iff_mem_invtSubmodule_adjoint [CompleteSpace E]
    [U.HasOrthogonalProjection] {A : E →L[𝕜] E} :
    U.IsReducing A ↔
      U ∈ invtSubmodule (A : End 𝕜 E) ∧ U ∈ invtSubmodule (A.adjoint : End 𝕜 E) := by
  rw [isReducing_iff, mem_invtSubmodule_adjoint_iff]

/-- A subspace with an orthogonal projection reduces the adjoint of a bounded operator `A` on a
Hilbert space exactly when it reduces `A`. -/
@[simp]
theorem ContinuousLinearMap.isReducing_adjoint_iff [CompleteSpace E] [U.HasOrthogonalProjection]
    {A : E →L[𝕜] E} : U.IsReducing A.adjoint ↔ U.IsReducing A := by
  rw [isReducing_iff_mem_invtSubmodule_adjoint, isReducing_iff_mem_invtSubmodule_adjoint,
    adjoint_adjoint, and_comm]

/-- On a finite-dimensional space, a subspace reduces an endomorphism `A` exactly when it is
invariant under both `A` and its adjoint. -/
theorem Module.End.isReducing_iff_mem_invtSubmodule_adjoint [FiniteDimensional 𝕜 E]
    {A : End 𝕜 E} : U.IsReducing A ↔ U ∈ A.invtSubmodule ∧ U ∈ invtSubmodule A.adjoint := by
  rw [isReducing_iff, End.mem_invtSubmodule_adjoint_iff]

/-- On a finite-dimensional space, a subspace reduces the adjoint of an endomorphism `A` exactly
when it reduces `A`. -/
@[simp]
theorem Module.End.isReducing_adjoint_iff [FiniteDimensional 𝕜 E] {A : End 𝕜 E} :
    U.IsReducing A.adjoint ↔ U.IsReducing A := by
  rw [isReducing_iff_mem_invtSubmodule_adjoint, isReducing_iff_mem_invtSubmodule_adjoint,
    LinearMap.adjoint_adjoint, and_comm]

/-- For an invariant subspace of a symmetric map, applying the complementary projection to
`A X - X M` is the same as forming the residual of the projected trial map. No isometry or
finite-dimensionality hypothesis is needed.

The corresponding DKPS projected-residual statement is in
`ForTauCeti/Analysis/InnerProductSpace/Residual/AngleEmbedding.lean` (Jon Crall and
GPT 5.6 High; Kitware, Apache-2.0). The proof uses invariant-projection commutation. -/
theorem LinearMap.IsSymmetric.sylvester_starProjection_orthogonal_comp
    {F : Type*} [AddCommGroup F] [Module 𝕜 F] {A : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : U ∈ Module.End.invtSubmodule A) (X : F →ₗ[𝕜] E) (M : F →ₗ[𝕜] F) :
    A ∘ₗ (Uᗮ.starProjection.toLinearMap ∘ₗ X) -
        (Uᗮ.starProjection.toLinearMap ∘ₗ X) ∘ₗ M =
      Uᗮ.starProjection.toLinearMap ∘ₗ (A ∘ₗ X - X ∘ₗ M) := by
  ext x
  have hU' := hA.orthogonalComplement_mem_invtSubmodule (p := U) hU
  have hcomm := hA.starProjection_apply_comm hU' (X x)
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, map_sub]
  rw [hcomm]

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] {U : Submodule 𝕜 E} [CompleteSpace U] {A : E →L[𝕜] E}

/-- The adjoint of the restriction of a bounded operator `A` to a complete subspace invariant
under both `A` and its adjoint is the restriction of the adjoint. -/
theorem adjoint_restrict (hA : ∀ x ∈ U, A x ∈ U) (hA' : ∀ x ∈ U, adjoint A x ∈ U) :
    adjoint (A.restrict hA) = (adjoint A).restrict hA' :=
  ((eq_adjoint_iff _ _).mpr fun x y ↦ by
    simp only [Submodule.coe_inner, coe_restrict_apply, adjoint_inner_left]).symm

/-- The restriction of a normal operator to a complete subspace invariant under both the operator
and its adjoint is normal. -/
theorem _root_.IsStarNormal.restrict (hN : IsStarNormal A) (hA : ∀ x ∈ U, A x ∈ U)
    (hA' : ∀ x ∈ U, adjoint A x ∈ U) : IsStarNormal (A.restrict hA) := by
  rw [isStarNormal_iff_norm_eq_adjoint, adjoint_restrict hA hA']
  intro x
  rw [← Submodule.norm_coe, ← Submodule.norm_coe, coe_restrict_apply, coe_restrict_apply]
  exact isStarNormal_iff_norm_eq_adjoint.mp hN x

end ContinuousLinearMap
