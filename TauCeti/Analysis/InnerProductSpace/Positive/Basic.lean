/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Invertibility of `1 + T` for a positive operator `T`

For a positive operator `T` on a possibly infinite-dimensional Hilbert space, `1 + T` is
invertible (`ContinuousLinearMap.IsPositive.isUnit_one_add`), because
`re ⟪(1 + T) x, x⟫ ≥ ‖x‖²` bounds it below. This applies in particular to `T = X†X`, which makes
`(1 + X†X)⁻¹` available in formulas such as the orthogonal projection onto a graph subspace.
-/

public section

namespace ContinuousLinearMap

open scoped InnerProductSpace InnerProduct

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- On a complete space, `1 + T` is invertible for every positive operator `T`, since
`re ⟪(1 + T) x, x⟫ = ‖x‖² + re ⟪T x, x⟫ ≥ ‖x‖²`. For instance `1 + X†X` is invertible, by
`ContinuousLinearMap.isPositive_adjoint_comp_self`. -/
theorem IsPositive.isUnit_one_add {T : E →L[𝕜] E} (hT : T.IsPositive) : IsUnit (1 + T) := by
  refine isUnit_of_forall_le_norm_inner_map _ one_pos fun x => ?_
  rw [NNReal.coe_one, mul_one]
  calc ‖x‖ ^ 2 ≤ RCLike.re ⟪(1 + T) x, x⟫_𝕜 := by
        rw [add_apply, one_apply_eq_self, inner_add_left, map_add, inner_self_eq_norm_sq]
        exact le_add_of_nonneg_right (hT.re_inner_nonneg_left x)
    _ ≤ ‖⟪(1 + T) x, x⟫_𝕜‖ := RCLike.re_le_norm _

end ContinuousLinearMap
