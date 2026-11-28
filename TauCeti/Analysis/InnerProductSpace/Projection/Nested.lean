/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Orthogonal projections onto nested subspaces

When `U ≤ V` admit orthogonal projections, `Uᗮ ⊓ V` also admits an orthogonal projection (without
completeness of `E`), with `(Uᗮ ⊓ V).starProjection = V.starProjection - U.starProjection` and
`‖x - U.starProjection x‖ ^ 2 = ‖x - V.starProjection x‖ ^ 2 + ‖(Uᗮ ⊓ V).starProjection x‖ ^ 2`.
-/

public section

noncomputable section

namespace Submodule

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {U V : Submodule 𝕜 E}

/-- When `U ≤ V` and both admit orthogonal projections, `V.starProjection x - U.starProjection x`
belongs to `Uᗮ ⊓ V`. -/
theorem starProjection_sub_mem_orthogonal_inf_of_le [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (h : U ≤ V) (x : E) :
    V.starProjection x - U.starProjection x ∈ Uᗮ ⊓ V := by
  refine ⟨(Submodule.mem_orthogonal U _).2 fun u hu ↦ ?_,
    V.sub_mem (V.starProjection_apply_mem x) (h (U.starProjection_apply_mem x))⟩
  rw [inner_sub_right, ← U.inner_starProjection_left_eq_right,
    ← V.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hu,
    Submodule.starProjection_eq_self_iff.mpr (h hu), sub_self]

private theorem inner_sub_starProjection_sub_eq_zero [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (x : E) {w : E} (hw : w ∈ Uᗮ ⊓ V) :
    ⟪x - (V.starProjection x - U.starProjection x), w⟫_𝕜 = 0 := by
  have hsplit : x - (V.starProjection x - U.starProjection x) =
      (x - V.starProjection x) + U.starProjection x := by abel
  rw [hsplit, inner_add_left, V.starProjection_inner_eq_zero x w hw.2,
    (Submodule.mem_orthogonal U w).mp hw.1 (U.starProjection x) (U.starProjection_apply_mem x),
    add_zero]

/-- When `U ≤ V` and both admit orthogonal projections, `Uᗮ ⊓ V` also admits an orthogonal
projection, without requiring completeness of `E`. -/
theorem hasOrthogonalProjection_orthogonal_inf_of_le [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (h : U ≤ V) :
    (Uᗮ ⊓ V).HasOrthogonalProjection where
  exists_orthogonal x := ⟨V.starProjection x - U.starProjection x,
    starProjection_sub_mem_orthogonal_inf_of_le h x,
    (Submodule.mem_orthogonal (Uᗮ ⊓ V) _).2 fun w hw ↦ by
      rw [← inner_conj_symm, inner_sub_starProjection_sub_eq_zero x hw, map_zero]⟩

/-- For nested subspaces `U ≤ V`, the orthogonal projection onto `Uᗮ ⊓ V` is pointwise the
difference `V.starProjection x - U.starProjection x`. -/
theorem starProjection_orthogonal_inf_apply_of_le [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] [(Uᗮ ⊓ V).HasOrthogonalProjection] (h : U ≤ V) (x : E) :
    (Uᗮ ⊓ V).starProjection x = V.starProjection x - U.starProjection x :=
  (Uᗮ ⊓ V).eq_starProjection_of_mem_of_inner_eq_zero
    (starProjection_sub_mem_orthogonal_inf_of_le h x) fun _ hw ↦
    inner_sub_starProjection_sub_eq_zero x hw

/-- For `U ≤ V`, `(Uᗮ ⊓ V).starProjection = V.starProjection - U.starProjection`. -/
theorem starProjection_orthogonal_inf_of_le [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] [(Uᗮ ⊓ V).HasOrthogonalProjection] (h : U ≤ V) :
    (Uᗮ ⊓ V).starProjection = V.starProjection - U.starProjection :=
  ContinuousLinearMap.ext (starProjection_orthogonal_inf_apply_of_le h)

/-- For nested subspaces `U ≤ V`, `‖x - U.starProjection x‖ ^ 2` splits orthogonally into
`‖x - V.starProjection x‖ ^ 2 + ‖(Uᗮ ⊓ V).starProjection x‖ ^ 2`. -/
theorem norm_sub_starProjection_sq_of_le [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] [(Uᗮ ⊓ V).HasOrthogonalProjection] (h : U ≤ V) (x : E) :
    ‖x - U.starProjection x‖ ^ 2 =
      ‖x - V.starProjection x‖ ^ 2 + ‖(Uᗮ ⊓ V).starProjection x‖ ^ 2 := by
  have hsum : x - U.starProjection x = (x - V.starProjection x) + (Uᗮ ⊓ V).starProjection x := by
    rw [starProjection_orthogonal_inf_apply_of_le h x]; abel
  rw [hsum, sq, sq, sq]
  exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
    (V.starProjection_inner_eq_zero x _ ((Uᗮ ⊓ V).starProjection_apply_mem x).2)

end Submodule
