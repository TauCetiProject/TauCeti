/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Norms of products of orthogonal projections

For submodules `U` and `V` of an inner product space admitting orthogonal projections `P_U` and
`P_V`, the two products `P_U P_V` and `P_V P_U` have the same operator norm. Since
`P_V P_U = (P_U P_V)†`, this is the identity `‖T‖ = ‖T†‖`, stated here without any completeness
hypothesis on the ambient space, where the adjoint of a bounded operator need not exist.

## Main results

* `Submodule.norm_starProjection_comp_starProjection_comm`: `‖P_U P_V‖ = ‖P_V P_U‖`.
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

end Submodule
