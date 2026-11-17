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

When `U ≤ V` are subspaces of an inner product space `E` that admit orthogonal projections, the
orthogonal complement of `U` inside `V`, namely `V ⊓ Uᗮ`, also admits an orthogonal projection
without any completeness assumption on `E`. Its projection equals the difference
`V.starProjection - U.starProjection`, the squared residual splits orthogonally as
`‖x - U.starProjection x‖ ^ 2 = ‖x - V.starProjection x‖ ^ 2 + ‖(V ⊓ Uᗮ).starProjection x‖ ^ 2`,
and when `V` is finite-dimensional,
`Module.finrank 𝕜 ↥(V ⊓ Uᗮ) = Module.finrank 𝕜 V - Module.finrank 𝕜 U`.

## Main results

* `Submodule.hasOrthogonalProjection_inf_orthogonal_of_le`: `V ⊓ Uᗮ` admits an orthogonal
  projection whenever `U ≤ V` and both `U` and `V` do.
* `Submodule.sup_inf_orthogonal_of_le`: `U ⊔ (V ⊓ Uᗮ) = V` when `U ≤ V` and `U` admits an
  orthogonal projection.
* `Submodule.starProjection_inf_orthogonal_of_le`:
  `(V ⊓ Uᗮ).starProjection = V.starProjection - U.starProjection`.
* `Submodule.starProjection_inf_orthogonal_apply_of_le`: pointwise form of the difference.
* `Submodule.norm_sub_starProjection_sq_of_le`: orthogonal Pythagorean split of the squared
  residual along `V` and `V ⊓ Uᗮ`.
* `Submodule.finrank_inf_orthogonal_of_le`: dimension formula for `V ⊓ Uᗮ`.
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
    ← V.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr hu,
    Submodule.starProjection_eq_self_iff.mpr (h hu), sub_self]

/-- When `U ≤ V` and both admit orthogonal projections, `V ⊓ Uᗮ` also admits an orthogonal
projection, without requiring completeness of `E`. -/
theorem hasOrthogonalProjection_inf_orthogonal_of_le [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (h : U ≤ V) :
    (V ⊓ Uᗮ).HasOrthogonalProjection where
  exists_orthogonal x := by
    refine ⟨V.starProjection x - U.starProjection x,
      starProjection_sub_mem_inf_orthogonal_of_le h x,
      (Submodule.mem_orthogonal (V ⊓ Uᗮ) _).2 fun w hw ↦ ?_⟩
    have hsplit : x - (V.starProjection x - U.starProjection x) =
        (x - V.starProjection x) + U.starProjection x := by abel
    rw [hsplit, inner_add_right]
    have h1 : ⟪w, x - V.starProjection x⟫_𝕜 = 0 :=
      (Submodule.mem_orthogonal V _).mp (V.sub_starProjection_mem_orthogonal x) w hw.1
    have h2 : ⟪w, U.starProjection x⟫_𝕜 = 0 := by
      rw [← inner_conj_symm]
      simp [(Submodule.mem_orthogonal U _).mp hw.2 (U.starProjection x)
        (U.starProjection_apply_mem x)]
    rw [h1, h2, add_zero]

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
    (V ⊓ Uᗮ).starProjection x = V.starProjection x - U.starProjection x := by
  refine (V ⊓ Uᗮ).eq_starProjection_of_mem_of_inner_eq_zero
    (starProjection_sub_mem_inf_orthogonal_of_le h x) fun w hw ↦ ?_
  have hsplit : x - (V.starProjection x - U.starProjection x) =
      (x - V.starProjection x) + U.starProjection x := by abel
  rw [hsplit, inner_add_left]
  have h1 : ⟪x - V.starProjection x, w⟫_𝕜 = 0 :=
    V.starProjection_inner_eq_zero x w hw.1
  have h2 : ⟪U.starProjection x, w⟫_𝕜 = 0 :=
    (Submodule.mem_orthogonal U w).mp hw.2 (U.starProjection x) (U.starProjection_apply_mem x)
  rw [h1, h2, add_zero]

/-- For nested subspaces `U ≤ V`, the orthogonal projection onto `V ⊓ Uᗮ` is
`V.starProjection - U.starProjection`. -/
theorem starProjection_inf_orthogonal_of_le [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] [(V ⊓ Uᗮ).HasOrthogonalProjection] (h : U ≤ V) :
    (V ⊓ Uᗮ).starProjection = V.starProjection - U.starProjection :=
  ContinuousLinearMap.ext (starProjection_inf_orthogonal_apply_of_le h)

/-- For nested subspaces `U ≤ V`, the squared residual `‖x - U.starProjection x‖ ^ 2` splits
orthogonally into `‖x - V.starProjection x‖ ^ 2 + ‖(V ⊓ Uᗮ).starProjection x‖ ^ 2`. -/
theorem norm_sub_starProjection_sq_of_le [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] [(V ⊓ Uᗮ).HasOrthogonalProjection] (h : U ≤ V) (x : E) :
    ‖x - U.starProjection x‖ ^ 2 =
      ‖x - V.starProjection x‖ ^ 2 + ‖(V ⊓ Uᗮ).starProjection x‖ ^ 2 := by
  have hsum : x - U.starProjection x =
      (x - V.starProjection x) + (V ⊓ Uᗮ).starProjection x := by
    rw [starProjection_inf_orthogonal_apply_of_le h x]
    abel
  have hortho : ⟪x - V.starProjection x, (V ⊓ Uᗮ).starProjection x⟫_𝕜 = 0 :=
    V.starProjection_inner_eq_zero x _ ((V ⊓ Uᗮ).starProjection_apply_mem x).1
  rw [hsum, sq, sq, sq]
  exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hortho

/-- For nested subspaces `U ≤ V` with `V` finite-dimensional, the dimension of `V ⊓ Uᗮ` is
`Module.finrank 𝕜 V - Module.finrank 𝕜 U`. -/
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
