/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic.Module

/-!
# Operator norm of maps out of a product

The continuous linear map `(x, y) ↦ f x + g y` out of a product (`ContinuousLinearMap.coprod`) has
operator norm at most `‖f‖ + ‖g‖` (`ContinuousLinearMap.opNorm_coprod_le`). This bounds solution
operators assembled from separate operators for each component of the data, for instance the
forcing and the initial datum of an evolution equation. A continuous linear map out of `𝕜 × 𝕜`
is determined by its values on the coordinate vectors
(`ContinuousLinearMap.apply_mk_eq_smul_add_smul`), and has operator norm at most
`‖f (1, 0)‖ + ‖f (0, 1)‖`
(`ContinuousLinearMap.opNorm_le_norm_apply_one_zero_add_norm_apply_zero_one`).

For the conformal linear map `(1, 0) ↦ (a, b)`, `(0, 1) ↦ (-b, a)` of the plane, with conformal
factor `a² + b²`, the sum `‖X‖² + ‖Y‖²` of the squared norms of the values of a linear map on the
coordinate vectors and the same sum after composing with the conformal map agree up to the factor
`a² + b²` and a factor `2` (`TauCeti.norm_sq_add_norm_sq_le_two_mul`,
`TauCeti.mul_norm_sq_add_norm_sq_le_two_mul`). These compare `W^{1,2}` densities under a
holomorphic change of coordinates.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]

/-- The operator norm of `(x, y) ↦ f x + g y` is at most `‖f‖ + ‖g‖`. -/
theorem opNorm_coprod_le (f : E →L[𝕜] G) (g : F →L[𝕜] G) : ‖f.coprod g‖ ≤ ‖f‖ + ‖g‖ := by
  rw [← comp_fst_add_comp_snd]
  exact (opNorm_add_le _ _).trans (add_le_add
    ((f.opNorm_comp_le _).trans (mul_le_of_le_one_right (norm_nonneg _) (norm_fst_le _ _ _)))
    ((g.opNorm_comp_le _).trans (mul_le_of_le_one_right (norm_nonneg _) (norm_snd_le _ _ _))))

/-- A continuous linear map out of `𝕜 × 𝕜` at `(a, b)` is `a` times its value at `(1, 0)` plus `b`
times its value at `(0, 1)`. -/
theorem apply_mk_eq_smul_add_smul (f : 𝕜 × 𝕜 →L[𝕜] G) (a b : 𝕜) :
    f (a, b) = a • f (1, 0) + b • f (0, 1) := by
  rw [← map_smul, ← map_smul, ← map_add]
  simp

/-- A continuous linear map out of `𝕜 × 𝕜` has operator norm at most the sum of the norms of its
values on the coordinate vectors. -/
theorem opNorm_le_norm_apply_one_zero_add_norm_apply_zero_one (f : 𝕜 × 𝕜 →L[𝕜] G) :
    ‖f‖ ≤ ‖f (1, 0)‖ + ‖f (0, 1)‖ := by
  refine f.opNorm_le_bound (by positivity) fun ⟨a, b⟩ ↦ ?_
  rw [f.apply_mk_eq_smul_add_smul a b, add_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul, mul_comm]
  · exact mul_le_mul_of_nonneg_left (_root_.norm_fst_le (a, b)) (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_left (_root_.norm_snd_le (a, b)) (norm_nonneg _)

end ContinuousLinearMap

namespace TauCeti

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- The elementary inequality behind the comparison of `W^{1,2}` densities under conformal
changes of coordinates. -/
private theorem add_sq_add_add_sq_le (a b x y : ℝ) :
    (|a| * x + |b| * y) ^ 2 + (|b| * x + |a| * y) ^ 2 ≤
      2 * ((a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2)) := by
  nlinarith [mul_nonneg (sq_nonneg (|a| - |b|)) (add_nonneg (sq_nonneg x) (sq_nonneg y)),
    mul_nonneg (mul_nonneg (abs_nonneg a) (abs_nonneg b)) (sq_nonneg (x - y)), sq_abs a, sq_abs b]

/-- Under the conformal linear map `(1, 0) ↦ (a, b)`, `(0, 1) ↦ (-b, a)` of the plane, the sum of
the squared norms of the two partial derivatives `X`, `Y` of a map grows at most by twice the
conformal factor `a² + b²`. -/
theorem norm_sq_add_norm_sq_le_two_mul (a b : ℝ) (X Y : E) :
    ‖a • X + b • Y‖ ^ 2 + ‖(-b) • X + a • Y‖ ^ 2 ≤
      2 * ((a ^ 2 + b ^ 2) * (‖X‖ ^ 2 + ‖Y‖ ^ 2)) := by
  have h₁ : ‖a • X + b • Y‖ ≤ |a| * ‖X‖ + |b| * ‖Y‖ :=
    (norm_add_le _ _).trans_eq (by rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs])
  have h₂ : ‖(-b) • X + a • Y‖ ≤ |b| * ‖X‖ + |a| * ‖Y‖ :=
    (norm_add_le _ _).trans_eq (by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg])
  have h₁' := pow_le_pow_left₀ (norm_nonneg _) h₁ 2
  have h₂' := pow_le_pow_left₀ (norm_nonneg _) h₂ 2
  linarith [add_sq_add_add_sq_le a b ‖X‖ ‖Y‖]

/-- Conversely, under the conformal linear map `(1, 0) ↦ (a, b)`, `(0, 1) ↦ (-b, a)`, the sum of
the squared norms of the two partial derivatives of a map, times the conformal factor `a² + b²`, is
at most twice the sum after the change of coordinates. -/
theorem mul_norm_sq_add_norm_sq_le_two_mul (a b : ℝ) (X Y : E) :
    (a ^ 2 + b ^ 2) * (‖X‖ ^ 2 + ‖Y‖ ^ 2) ≤
      2 * (‖a • X + b • Y‖ ^ 2 + ‖(-b) • X + a • Y‖ ^ 2) := by
  set P := a • X + b • Y
  set Q := (-b) • X + a • Y
  set d := a ^ 2 + b ^ 2
  have hd : 0 ≤ d := by positivity
  -- Inverting the conformal map: `d X = a P - b Q` and `d Y = b P + a Q`.
  have hX : d * ‖X‖ ≤ |a| * ‖P‖ + |b| * ‖Q‖ := by
    have h : d • X = a • P - b • Q := by simp only [P, Q, d]; module
    rw [← Real.norm_of_nonneg hd, ← norm_smul, h]
    exact (norm_sub_le _ _).trans_eq (by rw [norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs])
  have hY : d * ‖Y‖ ≤ |b| * ‖P‖ + |a| * ‖Q‖ := by
    have h : d • Y = b • P + a • Q := by simp only [P, Q, d]; module
    rw [← Real.norm_of_nonneg hd, ← norm_smul, h]
    exact (norm_add_le _ _).trans_eq (by rw [norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs])
  have hX' := pow_le_pow_left₀ (by positivity) hX 2
  have hY' := pow_le_pow_left₀ (by positivity) hY 2
  have key := add_sq_add_add_sq_le a b ‖P‖ ‖Q‖
  rcases hd.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]
    positivity
  · refine le_of_mul_le_mul_left ?_ hpos
    nlinarith

end TauCeti
