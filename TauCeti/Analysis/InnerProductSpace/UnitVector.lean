/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Coefficients against a unit vector

For a unit vector `ξ` in an inner product space over `ℝ` or `ℂ`, the coefficient `⟪ξ, x⟫` lies
within `‖x - ξ‖` of `1 = ⟪ξ, ξ⟫`. For instance, a matrix coefficient `g ↦ ⟪ξ, ρ g ξ⟫` of a unitary
representation is close to `1` wherever `ρ g` moves `ξ` little.

Over `ℝ`, splitting `d` into its component `⟪d, e⟫ e` along a vector `e` of norm at most `1` and
the remainder `d - ⟪d, e⟫ e` does not increase length: `⟪d, e⟫² + ‖d - ⟪d, e⟫ e‖² ≤ ‖d‖²`.

## Main results

* `TauCeti.norm_inner_sub_one_le`: `‖⟪ξ, x⟫ - 1‖ ≤ ‖x - ξ‖` for a unit vector `ξ`.
* `TauCeti.inner_sq_add_norm_sub_sq_le`: `⟪d, e⟫² + ‖d - ⟪d, e⟫ e‖² ≤ ‖d‖²` for `‖e‖ ≤ 1`.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- For a unit vector `ξ`, the coefficient `⟪ξ, x⟫` lies within `‖x - ξ‖` of `1`. -/
theorem norm_inner_sub_one_le {ξ : E} (hξ : ‖ξ‖ = 1) (x : E) : ‖⟪ξ, x⟫_𝕜 - 1‖ ≤ ‖x - ξ‖ := by
  rw [← inner_self_eq_one_of_norm_eq_one hξ, ← inner_sub_right]
  simpa [hξ] using norm_inner_le_norm (𝕜 := 𝕜) ξ (x - ξ)

/-- For `‖e‖ ≤ 1`, the component `⟪d, e⟫` of `d` along `e` and the remainder `d - ⟪d, e⟫ e`
together have length at most `‖d‖`. -/
theorem inner_sq_add_norm_sub_sq_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (d : F) {e : F} (he : ‖e‖ ≤ 1) : ⟪d, e⟫_ℝ ^ 2 + ‖d - ⟪d, e⟫_ℝ • e‖ ^ 2 ≤ ‖d‖ ^ 2 := by
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have : ‖e‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg e) he
  nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg ⟪d, e⟫_ℝ)]

end TauCeti
