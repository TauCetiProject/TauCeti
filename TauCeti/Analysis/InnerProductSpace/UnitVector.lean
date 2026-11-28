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

In a real inner product space the coefficient `⟪f, x⟫` against a vector `f` of the closed unit
ball is at most `‖x‖`, with equality at `f = ‖x‖⁻¹ • x`, so `‖x‖` is the supremum of these
coefficients.

Over `ℝ`, splitting `d` into its component `⟪d, e⟫ e` along a vector `e` of norm at most `1` and
the remainder `d - ⟪d, e⟫ e` does not increase length: `⟪d, e⟫² + ‖d - ⟪d, e⟫ e‖² ≤ ‖d‖²`.

## Main results

* `TauCeti.norm_inner_sub_one_le`: `‖⟪ξ, x⟫ - 1‖ ≤ ‖x - ξ‖` for a unit vector `ξ`.
* `TauCeti.norm_sub_le_sqrt_two_mul_norm_sub_inner_smul`: for real unit vectors with
  `⟪ξ, x⟫ ≥ 0`, the chord `‖x - ξ‖` is at most `√2` times the sine `‖x - ⟪ξ, x⟫ ξ‖`.
* `TauCeti.real_inner_inv_norm_smul_self`: `⟪‖x‖⁻¹ • x, x⟫ = ‖x‖`.
* `TauCeti.norm_eq_iSup_real_inner`: `‖x‖ = ⨆ ‖f‖ ≤ 1, ⟪f, x⟫`.
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
    simp only [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      hx, hξ, real_inner_comm x ξ]
    ring
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  rw [mul_pow, Real.sq_sqrt zero_le_two, h₁, h₂]
  nlinarith

section Real

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The coefficient of `x` against its normalization `‖x‖⁻¹ • x` is `‖x‖`; both sides are `0`
for `x = 0`. -/
theorem real_inner_inv_norm_smul_self (x : F) : ⟪‖x‖⁻¹ • x, x⟫_ℝ = ‖x‖ := by
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq, sq, ← mul_assoc, inv_mul_mul_self]

/-- **The norm as a supremum of coefficients.** In a real inner product space, `‖x‖` is the
supremum of `⟪f, x⟫` over the closed unit ball, attained at `‖x‖⁻¹ • x`. -/
theorem norm_eq_iSup_real_inner (x : F) : ‖x‖ = ⨆ f : {f : F // ‖f‖ ≤ 1}, ⟪f.val, x⟫_ℝ := by
  have hle (f : {f : F // ‖f‖ ≤ 1}) : ⟪f.val, x⟫_ℝ ≤ ‖x‖ :=
    (real_inner_le_norm f.val x).trans (mul_le_of_le_one_left (norm_nonneg x) f.property)
  have hball : ‖‖x‖⁻¹ • x‖ ≤ 1 := by
    rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_le_one_of_le₀ le_rfl (norm_nonneg x)
  have : Nonempty {f : F // ‖f‖ ≤ 1} := ⟨⟨_, hball⟩⟩
  refine le_antisymm ?_ (ciSup_le hle)
  exact (real_inner_inv_norm_smul_self x).symm.le.trans
    (le_ciSup (f := fun f : {f : F // ‖f‖ ≤ 1} ↦ ⟪f.val, x⟫_ℝ) ⟨‖x‖, Set.forall_mem_range.2 hle⟩
      ⟨_, hball⟩)

end Real

/-- For `‖e‖ ≤ 1`, the component `⟪d, e⟫` of `d` along `e` and the remainder `d - ⟪d, e⟫ e`
together have length at most `‖d‖`. -/
theorem inner_sq_add_norm_sub_sq_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (d : F) {e : F} (he : ‖e‖ ≤ 1) : ⟪d, e⟫_ℝ ^ 2 + ‖d - ⟪d, e⟫_ℝ • e‖ ^ 2 ≤ ‖d‖ ^ 2 := by
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have : ‖e‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg e) he
  nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg ⟪d, e⟫_ℝ)]

end TauCeti
