/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Semisimple

/-!
# Reducing subspaces

A subspace `U` of an inner product space *reduces* an endomorphism `A` when both `U` and its
orthogonal complement `Uᗮ` are invariant under `A`; when `E = U ⊕ Uᗮ`, the operator `A` is then
the direct sum of its restrictions to `U` and to `Uᗮ`. This file states reduction in terms of
Mathlib's invariant-subspace predicate `Module.End.invtSubmodule` and proves the basic
characterizations.

When `U` admits an orthogonal projection `P = U.starProjection`, reduction is exactly
commutation: `U` reduces `A` if and only if `P A = A P`; for such `U`, reduction is also
symmetric between `U` and `Uᗮ`. If moreover `A` is a bounded operator on a Hilbert space (or an
endomorphism of a finite-dimensional space), `U` reduces `A` if and only if it is invariant under
both `A` and `A†`, and reduction is preserved by taking adjoints. For a symmetric operator,
reduction is the same as invariance.

## Main definitions

* `Submodule.IsReducing U A`: the subspace `U` reduces the endomorphism `A`.

## Main statements

* `Submodule.isReducing_iff_commute_starProjection`: `U` reduces `A` if and only if `A` commutes
  with the orthogonal projection onto `U`; `Submodule.isReducing_coe_iff_commute_starProjection`
  is the same statement for bounded operators.
  Both require `U.HasOrthogonalProjection`.
* `Submodule.isReducing_orthogonal_iff`: for `U` with an orthogonal projection, `Uᗮ` reduces `A`
  if and only if `U` does.
* `Submodule.IsReducing.iSup`: the supremum of a family of reducing subspaces is reducing.
* `ContinuousLinearMap.isReducing_iff_mem_invtSubmodule_adjoint`,
  `Module.End.isReducing_iff_mem_invtSubmodule_adjoint`: `U` reduces `A` if and only if it is
  invariant under `A` and `A†`; the first is for bounded operators on a complete space `E` and
  `U` with an orthogonal projection, the second for endomorphisms of a finite-dimensional `E`.
* `ContinuousLinearMap.isReducing_adjoint_iff`, `Module.End.isReducing_adjoint_iff`: `U` reduces
  `A†` if and only if it reduces `A`, under the same respective hypotheses.
* `LinearMap.IsSymmetric.isReducing_iff`: an invariant subspace of a symmetric operator reduces it.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer (1990), §II.3.

The commutation criterion for bounded operators also appears, with a predicate stated through
`∀ x ∈ U, A x ∈ U`, in the
[AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(Kitware, Inc.; Apache-2.0), `ForTauCeti/Analysis/InnerProductSpace/ReducingSubspace.lean`.
-/

public section

open Module End

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {U V : Submodule 𝕜 E} {A : End 𝕜 E}

/-- A subspace `U` *reduces* an endomorphism `A` when both `U` and its orthogonal complement `Uᗮ`
are invariant under `A`. -/
structure IsReducing (U : Submodule 𝕜 E) (A : End 𝕜 E) : Prop where
  /-- The subspace is invariant. -/
  mem_invtSubmodule : U ∈ A.invtSubmodule
  /-- The orthogonal complement of the subspace is invariant. -/
  orthogonal_mem_invtSubmodule : Uᗮ ∈ A.invtSubmodule

/-- Unbundled form of `Submodule.IsReducing`. -/
theorem isReducing_iff : U.IsReducing A ↔ U ∈ A.invtSubmodule ∧ Uᗮ ∈ A.invtSubmodule :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

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

/-- A subspace with an orthogonal projection reduces `A` exactly when its orthogonal complement
does. -/
@[simp]
theorem isReducing_orthogonal_iff [U.HasOrthogonalProjection] :
    Uᗮ.IsReducing A ↔ U.IsReducing A := by
  simp only [isReducing_iff, orthogonal_orthogonal, and_comm]

alias ⟨_, IsReducing.orthogonal⟩ := isReducing_orthogonal_iff

/-- A subspace with an orthogonal projection reduces an endomorphism `A` exactly when `A`
commutes with the orthogonal projection onto it. -/
theorem isReducing_iff_commute_starProjection [U.HasOrthogonalProjection] :
    U.IsReducing A ↔ Commute (U.starProjection : End 𝕜 E) A := by
  rw [LinearMap.IsIdempotentElem.commute_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap (isIdempotentElem_starProjection U)),
    isReducing_iff, range_starProjection, ker_starProjection]

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

/-- A subspace reduces a symmetric operator exactly when it is invariant under it. -/
theorem LinearMap.IsSymmetric.isReducing_iff {A : End 𝕜 E} (hA : A.IsSymmetric) :
    U.IsReducing A ↔ U ∈ A.invtSubmodule :=
  ⟨IsReducing.mem_invtSubmodule, fun h ↦ ⟨h, hA.orthogonalComplement_mem_invtSubmodule h⟩⟩
