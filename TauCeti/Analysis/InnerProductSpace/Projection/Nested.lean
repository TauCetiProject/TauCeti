/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Orthogonal projections onto nested subspaces

When `U ≤ V` admit orthogonal projections, `V ⊓ Uᗮ` also admits an orthogonal projection (without
completeness of `E`), with `(V ⊓ Uᗮ).starProjection = V.starProjection - U.starProjection`,
`‖x - U.starProjection x‖ ^ 2 = ‖x - V.starProjection x‖ ^ 2 + ‖(V ⊓ Uᗮ).starProjection x‖ ^ 2`,
and `Module.finrank 𝕜 ↥(V ⊓ Uᗮ) = Module.finrank 𝕜 V - Module.finrank 𝕜 U` when `V` is
finite-dimensional.
-/

public section

noncomputable section

namespace Submodule

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {U V : Submodule 𝕜 E}

/-- When `U ≤ V` and both admit orthogonal projections, `V.starProjection x - U.starProjection x`
belongs to `V ⊓ Uᗮ`. -/
theorem starProjection_sub_mem_inf_orthogonal_of_le [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (h : U ≤ V) (x : E) :
    V.starProjection x - U.starProjection x ∈ V ⊓ Uᗮ := by
  refine ⟨V.sub_mem (V.starProjection_apply_mem x) (h (U.starProjection_apply_mem x)),
    (Submodule.mem_orthogonal U _).2 fun u hu ↦ ?_⟩
  rw [inner_sub_right, ← U.inner_starProjection_left_eq_right,
    ← V.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hu,
    Submodule.starProjection_eq_self_iff.mpr (h hu), sub_self]

private theorem inner_sub_starProjection_sub_eq_zero [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (x : E) {w : E} (hw : w ∈ V ⊓ Uᗮ) :
    ⟪x - (V.starProjection x - U.starProjection x), w⟫_𝕜 = 0 := by
  have hsplit : x - (V.starProjection x - U.starProjection x) =
      (x - V.starProjection x) + U.starProjection x := by abel
  rw [hsplit, inner_add_left, V.starProjection_inner_eq_zero x w hw.1,
    (Submodule.mem_orthogonal U w).mp hw.2 (U.starProjection x) (U.starProjection_apply_mem x),
    add_zero]

/-- When `U ≤ V` and both admit orthogonal projections, `V ⊓ Uᗮ` also admits an orthogonal
projection, without requiring completeness of `E`. -/
theorem hasOrthogonalProjection_inf_orthogonal_of_le [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (h : U ≤ V) :
    (V ⊓ Uᗮ).HasOrthogonalProjection where
  exists_orthogonal x := ⟨V.starProjection x - U.starProjection x,
    starProjection_sub_mem_inf_orthogonal_of_le h x,
    (Submodule.mem_orthogonal (V ⊓ Uᗮ) _).2 fun w hw ↦ by
      rw [← inner_conj_symm, inner_sub_starProjection_sub_eq_zero x hw, map_zero]⟩

/-- Orthogonal modular law: for `U ≤ V` with `U` admitting an orthogonal projection,
`U ⊔ (V ⊓ Uᗮ) = V`. -/
theorem sup_inf_orthogonal_of_le [U.HasOrthogonalProjection] (h : U ≤ V) :
    U ⊔ (V ⊓ Uᗮ) = V := by
  refine le_antisymm (sup_le h inf_le_left) fun v hv ↦ ?_
  rw [← add_sub_cancel (U.starProjection v) v]
  exact Submodule.add_mem_sup (U.starProjection_apply_mem v)
    ⟨V.sub_mem hv (h (U.starProjection_apply_mem v)), U.sub_starProjection_mem_orthogonal v⟩

/-- For nested subspaces `U ≤ V`, the orthogonal projection onto `V ⊓ Uᗮ` is pointwise the
difference `V.starProjection x - U.starProjection x`. -/
theorem starProjection_inf_orthogonal_apply_of_le [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] [(V ⊓ Uᗮ).HasOrthogonalProjection] (h : U ≤ V) (x : E) :
    (V ⊓ Uᗮ).starProjection x = V.starProjection x - U.starProjection x :=
  (V ⊓ Uᗮ).eq_starProjection_of_mem_of_inner_eq_zero
    (starProjection_sub_mem_inf_orthogonal_of_le h x) fun _ hw ↦
    inner_sub_starProjection_sub_eq_zero x hw

/-- For `U ≤ V`, `(V ⊓ Uᗮ).starProjection = V.starProjection - U.starProjection`. -/
theorem starProjection_inf_orthogonal_of_le [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] [(V ⊓ Uᗮ).HasOrthogonalProjection] (h : U ≤ V) :
    (V ⊓ Uᗮ).starProjection = V.starProjection - U.starProjection :=
  ContinuousLinearMap.ext (starProjection_inf_orthogonal_apply_of_le h)

/-- For nested subspaces `U ≤ V`, `‖x - U.starProjection x‖ ^ 2` splits orthogonally into
`‖x - V.starProjection x‖ ^ 2 + ‖(V ⊓ Uᗮ).starProjection x‖ ^ 2`. -/
theorem norm_sub_starProjection_sq_of_le [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] [(V ⊓ Uᗮ).HasOrthogonalProjection] (h : U ≤ V) (x : E) :
    ‖x - U.starProjection x‖ ^ 2 =
      ‖x - V.starProjection x‖ ^ 2 + ‖(V ⊓ Uᗮ).starProjection x‖ ^ 2 := by
  have hsum : x - U.starProjection x = (x - V.starProjection x) + (V ⊓ Uᗮ).starProjection x := by
    rw [starProjection_inf_orthogonal_apply_of_le h x]; abel
  rw [hsum, sq, sq, sq]
  exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
    (V.starProjection_inner_eq_zero x _ ((V ⊓ Uᗮ).starProjection_apply_mem x).1)

/-- For nested subspaces `U ≤ V` with `V` finite-dimensional,
`Module.finrank 𝕜 ↥(V ⊓ Uᗮ) = Module.finrank 𝕜 V - Module.finrank 𝕜 U`. -/
theorem finrank_inf_orthogonal_of_le [FiniteDimensional 𝕜 V] (h : U ≤ V) :
    Module.finrank 𝕜 ↥(V ⊓ Uᗮ) = Module.finrank 𝕜 V - Module.finrank 𝕜 U := by
  have : FiniteDimensional 𝕜 U := Submodule.finiteDimensional_of_le h
  have : FiniteDimensional 𝕜 ↥(V ⊓ Uᗮ) := Submodule.finiteDimensional_of_le inf_le_left
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U (V ⊓ Uᗮ)
  have hinf : U ⊓ (V ⊓ Uᗮ) = ⊥ := by
    rw [← inf_assoc, inf_eq_left.mpr h, U.inf_orthogonal_eq_bot]
  rw [sup_inf_orthogonal_of_le h, hinf, finrank_bot, add_zero] at hsum
  omega

end Submodule
