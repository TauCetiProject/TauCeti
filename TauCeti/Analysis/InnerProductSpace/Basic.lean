/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Norm bounds from the inner product of a vector with itself

Since `‖⟪z, z⟫‖ = ‖z‖²`, a bound `‖⟪z, z⟫‖ ≤ K ‖z‖` with `0 ≤ K` bounds the norm of `z` by `K`
(`TauCeti.norm_le_of_norm_inner_self_le`). This is how a vector paired against itself is
controlled by a dual-norm estimate `|⟪z, y⟫| ≤ K ‖y‖`.

## Main results

* `TauCeti.norm_le_of_norm_inner_self_le`: `‖⟪z, z⟫‖ ≤ K ‖z‖` and `0 ≤ K` imply `‖z‖ ≤ K`.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A vector `z` of an inner product space with `‖⟪z, z⟫‖ ≤ K ‖z‖`, for `0 ≤ K`, has norm at most
`K`. -/
theorem norm_le_of_norm_inner_self_le {z : E} {K : ℝ} (hK : 0 ≤ K) (h : ‖⟪z, z⟫_𝕜‖ ≤ K * ‖z‖) :
    ‖z‖ ≤ K := by
  rcases (norm_nonneg z).eq_or_lt with hz | hz
  · rw [← hz]
    exact hK
  refine le_of_mul_le_mul_right ?_ hz
  rwa [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm, sq] at h

end TauCeti
