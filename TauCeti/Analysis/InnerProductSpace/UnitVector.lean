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
representation is close to `1` wherever `ρ g` moves `ξ` little. For real unit vectors with
`⟪ξ, x⟫ ≥ 0`, the distance `‖x - ξ‖` is at most `√2` times the sine `‖x - ⟪ξ, x⟫ ξ‖` of the
angle between them.

## Main results

* `TauCeti.norm_inner_sub_one_le`: `‖⟪ξ, x⟫ - 1‖ ≤ ‖x - ξ‖` for a unit vector `ξ`.
* `TauCeti.norm_sub_le_sqrt_two_mul_norm_sub_inner_smul`: for real unit vectors with
  `⟪ξ, x⟫ ≥ 0`, the chord `‖x - ξ‖` is at most `√2` times the sine `‖x - ⟪ξ, x⟫ ξ‖`.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- For a unit vector `ξ`, the coefficient `⟪ξ, x⟫` lies within `‖x - ξ‖` of `1`. -/
theorem norm_inner_sub_one_le {ξ : E} (hξ : ‖ξ‖ = 1) (x : E) : ‖⟪ξ, x⟫_𝕜 - 1‖ ≤ ‖x - ξ‖ := by
  rw [← inner_self_eq_one_of_norm_eq_one hξ, ← inner_sub_right]
  simpa [hξ] using norm_inner_le_norm (𝕜 := 𝕜) ξ (x - ξ)

/-- For real unit vectors `ξ` and `x` with `⟪ξ, x⟫ ≥ 0`, the chord `‖x - ξ‖` is at most `√2`
times the sine `‖x - ⟪ξ, x⟫ ξ‖` of their angle: with `ρ = ⟪ξ, x⟫ ∈ [0, 1]`,
`‖x - ξ‖² = 2 (1 - ρ) ≤ 2 (1 - ρ²) = 2 ‖x - ρ ξ‖²`. -/
theorem norm_sub_le_sqrt_two_mul_norm_sub_inner_smul {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {ξ x : F} (hξ : ‖ξ‖ = 1) (hx : ‖x‖ = 1) (h : 0 ≤ ⟪ξ, x⟫_ℝ) :
    ‖x - ξ‖ ≤ √2 * ‖x - ⟪ξ, x⟫_ℝ • ξ‖ := by
  have hρ : ⟪ξ, x⟫_ℝ ≤ 1 := by simpa [hξ, hx] using real_inner_le_norm ξ x
  have h₁ : ‖x - ξ‖ ^ 2 = 2 - 2 * ⟪ξ, x⟫_ℝ := by
    rw [norm_sub_sq_real, hx, hξ, real_inner_comm]
    ring
  have h₂ : ‖x - ⟪ξ, x⟫_ℝ • ξ‖ ^ 2 = 1 - ⟪ξ, x⟫_ℝ ^ 2 := by
    rw [norm_sub_sq_real, hx, inner_smul_right, real_inner_comm, norm_smul, hξ, Real.norm_eq_abs,
      mul_one, sq_abs]
    ring
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [mul_pow, Real.sq_sqrt zero_le_two, h₁, h₂]
  nlinarith

end TauCeti
