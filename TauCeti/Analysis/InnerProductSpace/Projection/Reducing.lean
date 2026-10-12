/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Semisimple
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.Analysis.InnerProductSpace.Projection.Block

/-!
# Reducing subspaces

A submodule `U` of an inner product space *reduces* an endomorphism `A` when both `U` and its
orthogonal complement `Uᗮ` are `A`-invariant (`Submodule.Reduces`). Invariance is recorded by
Mathlib's `Module.End.invtSubmodule`.

When `U` also admits an orthogonal projection `P_U` (`[U.HasOrthogonalProjection]`), so that
`E = U ⊕ Uᗮ`, a reducing subspace splits `A` along this decomposition into an operator on `U` and
an operator on `Uᗮ`, which is how restrictions of self-adjoint operators to spectral subspaces are
formed. If moreover `E` is complete, then `U` is complete
(`Submodule.completeSpace_of_hasOrthogonalProjection` in
`TauCeti.Analysis.InnerProductSpace.Projection.Completeness`), so it is itself a Hilbert space on
which the operator restricts.

## Main definitions

* `Submodule.Reduces U A`: both `U` and `Uᗮ` are invariant under `A`.

## Main results

* `Submodule.reduces_orthogonal_iff`: `Uᗮ` reduces `A` exactly when `U` does.
* `Submodule.reduces_iff_commute_starProjection`: `U` reduces `A` exactly when `P_U` commutes
  with `A`; `Submodule.reduces_iff_commute_reflection` gives the same for the reflection
  `R_U = 2 P_U - 1`.
* `LinearMap.IsSymmetric.reduces_iff`: for a symmetric operator, reducing subspaces are exactly
  the invariant ones.
* `Submodule.reduces_adjoint_iff`: `U` reduces a bounded operator exactly when it reduces its
  adjoint.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer GTM 96, 1990, §II.3.
-/

public section

noncomputable section

open Module.End

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Submodule

/-! ### Reducing subspaces -/

/-- A submodule `U` *reduces* an endomorphism `A` when both `U` and its orthogonal complement
`Uᗮ` are invariant under `A`. -/
def Reduces (U : Submodule 𝕜 E) (A : Module.End 𝕜 E) : Prop :=
  U ∈ A.invtSubmodule ∧ Uᗮ ∈ A.invtSubmodule

variable {U : Submodule 𝕜 E} {A : Module.End 𝕜 E}

theorem reduces_iff : U.Reduces A ↔ U ∈ A.invtSubmodule ∧ Uᗮ ∈ A.invtSubmodule :=
  Iff.rfl

theorem Reduces.mk (hU : U ∈ A.invtSubmodule) (hU' : Uᗮ ∈ A.invtSubmodule) : U.Reduces A :=
  ⟨hU, hU'⟩

theorem Reduces.mem_invtSubmodule (h : U.Reduces A) : U ∈ A.invtSubmodule :=
  h.1

theorem Reduces.orthogonal_mem_invtSubmodule (h : U.Reduces A) : Uᗮ ∈ A.invtSubmodule :=
  h.2

variable (A) in
@[simp]
theorem reduces_bot : (⊥ : Submodule 𝕜 E).Reduces A := by
  simp [reduces_iff, invtSubmodule.bot_mem, invtSubmodule.top_mem]

variable (A) in
@[simp]
theorem reduces_top : (⊤ : Submodule 𝕜 E).Reduces A := by
  simp [reduces_iff, invtSubmodule.bot_mem, invtSubmodule.top_mem]

/-- The orthogonal complement of a projected subspace reduces exactly the operators the subspace
reduces. -/
@[simp]
theorem reduces_orthogonal_iff [U.HasOrthogonalProjection] : Uᗮ.Reduces A ↔ U.Reduces A := by
  rw [reduces_iff, reduces_iff, orthogonal_orthogonal, and_comm]

alias ⟨_, Reduces.orthogonal⟩ := reduces_orthogonal_iff

/-- A projected subspace reduces an operator exactly when the orthogonal projection onto it
commutes with the operator. -/
theorem reduces_iff_commute_starProjection [U.HasOrthogonalProjection] :
    U.Reduces A ↔ Commute (U.starProjection : Module.End 𝕜 E) A := by
  rw [LinearMap.IsIdempotentElem.commute_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap U.isIdempotentElem_starProjection),
    reduces_iff]
  simp only [range_starProjection, ker_starProjection]

/-- The bounded-operator form of `Submodule.reduces_iff_commute_starProjection`: a projected
subspace reduces a bounded operator exactly when the orthogonal projection onto it commutes with
the operator in `E →L[𝕜] E`. -/
theorem reduces_iff_commute_starProjection' [U.HasOrthogonalProjection] {A : E →L[𝕜] E} :
    U.Reduces A ↔ Commute U.starProjection A := by
  rw [ContinuousLinearMap.IsIdempotentElem.commute_iff U.isIdempotentElem_starProjection,
    reduces_iff]
  simp only [range_starProjection, ker_starProjection]

/-- A projected subspace reduces a bounded operator exactly when the reflection across it commutes
with the operator. -/
theorem reduces_iff_commute_reflection [U.HasOrthogonalProjection] {A : E →L[𝕜] E} :
    U.Reduces A ↔ Commute (U.reflection : E →L[𝕜] E) A := by
  rw [commute_reflection_iff, reduces_iff_commute_starProjection']

variable (U) in
/-- A projected subspace reduces the orthogonal projection onto it. -/
theorem reduces_starProjection [U.HasOrthogonalProjection] :
    U.Reduces (U.starProjection : Module.End 𝕜 E) :=
  reduces_iff_commute_starProjection.2 (Commute.refl _)

/-- A projected subspace reduces a bounded operator exactly when it reduces its adjoint. -/
@[simp]
theorem reduces_adjoint_iff [CompleteSpace E] [U.HasOrthogonalProjection] {A : E →L[𝕜] E} :
    U.Reduces (ContinuousLinearMap.adjoint A) ↔ U.Reduces A := by
  rw [reduces_iff, reduces_iff, ContinuousLinearMap.mem_invtSubmodule_adjoint_iff,
    ContinuousLinearMap.mem_invtSubmodule_adjoint_iff, orthogonal_orthogonal, and_comm]

end Submodule

namespace LinearMap.IsSymmetric

variable {A : Module.End 𝕜 E} {U : Submodule 𝕜 E}

/-- For a symmetric operator, a submodule is reducing exactly when it is invariant. -/
theorem reduces_iff (hA : A.IsSymmetric) : U.Reduces A ↔ U ∈ A.invtSubmodule :=
  ⟨Submodule.Reduces.mem_invtSubmodule,
    fun h ↦ ⟨h, hA.orthogonalComplement_mem_invtSubmodule h⟩⟩

/-- Each eigenspace of a symmetric operator reduces it. -/
theorem reduces_eigenspace (hA : A.IsSymmetric) (μ : 𝕜) : (eigenspace A μ).Reduces A :=
  hA.reduces_iff.2 (eigenspace_mem_invtSubmodule A μ)

end LinearMap.IsSymmetric
