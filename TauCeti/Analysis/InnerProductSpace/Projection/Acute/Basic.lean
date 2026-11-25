/-
Copyright (c) 2026 The Tau Ceti contributors and Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Jon Crall, GPT 5.6 High, OpenAI GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.Gap

/-!
# Acute pairs of subspaces

Let `U` and `V` be subspaces of an inner product space with orthogonal projections `P_U` and `P_V`.

The pair `(U, V)` is *acute* (`Submodule.IsAcute`) when `P_V` is injective on `U` and `P_U` is
injective on `V`, that is, when no nonzero vector of one subspace is orthogonal to the other. A
pair whose gap `‖P_U - P_V‖` is less than `1` is acute, with no completeness or dimension
hypothesis.

## Main definitions

* `Submodule.IsAcute U V`: the orthogonal projection onto each subspace is injective on the other.

## Main results

* `Submodule.isAcute_iff_disjoint`: acuteness in terms of the subspaces `U ⊓ Vᗮ` and `V ⊓ Uᗮ`.
* `Submodule.IsAcute.of_projectionGap_lt_one`: a pair with gap less than `1` is acute.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), §I.6.8.
-/

public section

noncomputable section

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-! ### Acute pairs -/

/-- A pair of subspaces `(U, V)` is *acute* when the orthogonal projection onto each of them is
injective on the other: no nonzero vector of one subspace is orthogonal to the other. -/
structure IsAcute : Prop where
  /-- The orthogonal projection onto `V` is injective on `U`. -/
  injOn_left : Set.InjOn V.starProjection U
  /-- The orthogonal projection onto `U` is injective on `V`. -/
  injOn_right : Set.InjOn U.starProjection V

variable {U V} in
/-- A pair is acute exactly when `U ⊓ Vᗮ = ⊥` and `V ⊓ Uᗮ = ⊥`. -/
theorem isAcute_iff_disjoint : U.IsAcute V ↔ Disjoint U Vᗮ ∧ Disjoint V Uᗮ := by
  rw [← injOn_starProjection_iff_disjoint, ← injOn_starProjection_iff_disjoint]
  exact ⟨fun h ↦ ⟨h.injOn_left, h.injOn_right⟩, fun h ↦ ⟨h.1, h.2⟩⟩

variable {U V} in
theorem IsAcute.symm (h : U.IsAcute V) : V.IsAcute U :=
  ⟨h.injOn_right, h.injOn_left⟩

theorem isAcute_comm : U.IsAcute V ↔ V.IsAcute U :=
  ⟨IsAcute.symm, IsAcute.symm⟩

/-- Every subspace makes an acute pair with itself. -/
theorem isAcute_self : U.IsAcute U :=
  isAcute_iff_disjoint.2 ⟨U.orthogonal_disjoint, U.orthogonal_disjoint⟩

/-- **Acuteness from the projection gap.** A pair of subspaces with `‖P_U - P_V‖ < 1` is acute. -/
theorem IsAcute.of_projectionGap_lt_one (h : U.projectionGap V < 1) : U.IsAcute V :=
  isAcute_iff_disjoint.2
    ⟨disjoint_orthogonal_of_directedProjectionGap_lt_one U V
        ((directedProjectionGap_le_projectionGap U V).trans_lt h),
      disjoint_orthogonal_of_directedProjectionGap_lt_one V U
        ((directedProjectionGap_le_projectionGap V U).trans_lt (projectionGap_comm U V ▸ h))⟩

end Submodule
