/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Semisimple

/-!
# Reducing subspaces of inner-product spaces

A subspace reduces an endomorphism when both it and its orthogonal complement are invariant.
For a symmetric endomorphism, invariance of the subspace alone is enough. When an orthogonal
projection exists, reduction is equivalently commutation with that projection.
-/

public section

open Module

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A subspace is reducing for an endomorphism when both it and its orthogonal complement are
invariant under the endomorphism. -/
def IsReducing (U : Submodule 𝕜 E) (A : Module.End 𝕜 E) : Prop :=
  U ∈ A.invtSubmodule ∧ Uᗮ ∈ A.invtSubmodule

/-- A subspace is reducing exactly when it and its orthogonal complement are invariant. -/
@[simp]
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

end Submodule
