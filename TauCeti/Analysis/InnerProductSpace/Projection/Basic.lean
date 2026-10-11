/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Products of orthogonal projections

For submodules `U` and `V` of an inner product space admitting orthogonal projections `P_U` and
`P_V`, the two products `P_U P_V` and `P_V P_U` have the same operator norm. Since
`P_V P_U = (P_U P_V)†`, this is the identity `‖T‖ = ‖T†‖`, stated here without any completeness
hypothesis on the ambient space, where the adjoint of a bounded operator need not exist.

A map `T P_U` that factors through the projection onto a finite-dimensional `U` has rank at most
`dim U`. For subspaces `U` and `V` of the same finite dimension, `U ⊓ Vᗮ` and `V ⊓ Uᗮ` have the
same dimension.

## Main results

* `Submodule.norm_starProjection_comp_starProjection_comm`: `‖P_U P_V‖ = ‖P_V P_U‖`.
* `Submodule.finrank_range_comp_starProjection_le`: `rank (T P_U) ≤ dim U`.
* `Submodule.finrank_inf_orthogonal_comm`: `dim (U ⊓ Vᗮ) = dim (V ⊓ Uᗮ)` when `dim U = dim V`.
-/

public section

noncomputable section

namespace Submodule

open ContinuousLinearMap
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- One half of `norm_starProjection_comp_starProjection_comm`. -/
private theorem norm_starProjection_comp_starProjection_le :
    ‖U.starProjection ∘L V.starProjection‖ ≤ ‖V.starProjection ∘L U.starProjection‖ := by
  -- For `y = P_U P_V x`, `‖y‖² = Re ⟪x, P_V P_U y⟫` because both projections are symmetric and
  -- `P_U y = y`.
  refine opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  set y := U.starProjection (V.starProjection x)
  have hy : U.starProjection y = y := starProjection_eq_self_iff.mpr (U.starProjection_apply_mem _)
  have hinner : ⟪y, y⟫_𝕜 = ⟪x, V.starProjection y⟫_𝕜 :=
    calc ⟪y, y⟫_𝕜 = ⟪V.starProjection x, U.starProjection y⟫_𝕜 :=
          inner_starProjection_left_eq_right U _ _
      _ = ⟪x, V.starProjection y⟫_𝕜 := by rw [hy, inner_starProjection_left_eq_right]
  have key : ‖y‖ * ‖y‖ ≤ ‖V.starProjection ∘L U.starProjection‖ * ‖x‖ * ‖y‖ := by
    calc ‖y‖ * ‖y‖ = RCLike.re ⟪x, V.starProjection y⟫_𝕜 := by
          rw [← inner_self_eq_norm_mul_norm (𝕜 := 𝕜), hinner]
      _ ≤ ‖x‖ * ‖(V.starProjection ∘L U.starProjection) y‖ := by
          rw [comp_apply, hy]
          exact re_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖V.starProjection ∘L U.starProjection‖ * ‖y‖) := by
          gcongr
          exact le_opNorm _ _
      _ = ‖V.starProjection ∘L U.starProjection‖ * ‖x‖ * ‖y‖ := by ring
  rcases (norm_nonneg y).eq_or_lt with h | h
  · rw [comp_apply, ← h]
    positivity
  · exact le_of_mul_le_mul_right key h

/-- The two products of a pair of orthogonal projections have the same operator norm, that is,
`‖T‖ = ‖T†‖` for `T = P_U P_V`. No completeness of `E` is assumed. -/
theorem norm_starProjection_comp_starProjection_comm :
    ‖U.starProjection ∘L V.starProjection‖ = ‖V.starProjection ∘L U.starProjection‖ :=
  (norm_starProjection_comp_starProjection_le U V).antisymm
    (norm_starProjection_comp_starProjection_le V U)

/-- A map `T P_U` that factors through the projection onto `U` has rank at most `dim U`. -/
theorem finrank_range_comp_starProjection_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 U] (T : E →L[𝕜] F) :
    Module.finrank 𝕜 (LinearMap.range ((T ∘L U.starProjection : E →L[𝕜] F) : E →ₗ[𝕜] F)) ≤
      Module.finrank 𝕜 U := by
  have hU : LinearMap.range (U.starProjection : E →ₗ[𝕜] E) = U := range_starProjection U
  rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp, hU]
  exact finrank_map_le _ _

omit [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] in
/-- For subspaces of the same dimension, `U ⊓ Vᗮ` and `V ⊓ Uᗮ` have the same dimension. -/
theorem finrank_inf_orthogonal_comm [FiniteDimensional 𝕜 E]
    (h : Module.finrank 𝕜 U = Module.finrank 𝕜 V) :
    Module.finrank 𝕜 ↥(U ⊓ Vᗮ) = Module.finrank 𝕜 ↥(V ⊓ Uᗮ) := by
  have h₁ := finrank_sup_add_finrank_inf_eq U Vᗮ
  have h₂ := finrank_add_finrank_orthogonal (U ⊔ Vᗮ)
  rw [← inf_orthogonal, orthogonal_orthogonal, inf_comm] at h₂
  have h₃ := finrank_add_finrank_orthogonal V
  omega

end Submodule
