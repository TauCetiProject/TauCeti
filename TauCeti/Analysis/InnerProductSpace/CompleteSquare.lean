/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Completing the square for a weighted sum of squared distances

In a real inner product space, a weighted sum `a ‖y‖² + b ‖x - y‖²` of the squared distances from
`y` to the two points `0` and `x` is, as a function of `y`, a multiple of the squared distance
from `y` to the weighted centre `(b / (a + b)) • x`, plus a constant:

`a ‖y‖² + b ‖x - y‖² = (a + b) ‖y - (b / (a + b)) • x‖² + (a b / (a + b)) ‖x‖²`

whenever `a + b ≠ 0`. This is the identity behind products of Gaussians being Gaussians.

Specialized to the weights `1 - t` and `t` for `t ∈ [0, 1]`, it is the identity
`d(x, (1 - t) a + t b) ^ 2 + t (1 - t) d(a, b) ^ 2 = (1 - t) d(x, a) ^ 2 + t d(x, b) ^ 2`,
which we record in `ℝ≥0∞` for use in extended-valued integral estimates.

## Main declarations

* `TauCeti.mul_norm_sq_add_mul_norm_sub_sq`: the completed-square identity above.
* `TauCeti.norm_sq_div_two_add_norm_sub_sq_div`: its case `a = 1 / 2`, `b = 1 / (2τ)`. For
  `τ > 0` this objective is minimized exactly at `x / (1 + τ)`, the proximal point of
  `‖·‖² / 2` at `x`.
* `TauCeti.edist_smul_add_smul_sq_add`: the convex-combination form of the identity, for extended
  distances.
-/

public section

namespace TauCeti

open scoped RealInnerProductSpace

variable {F : Type*} [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Completing the square** for a weighted sum of squared distances: if `a + b ≠ 0`, then
`a ‖y‖² + b ‖x - y‖² = (a + b) ‖y - (b / (a + b)) • x‖² + (a b / (a + b)) ‖x‖²`. -/
theorem mul_norm_sq_add_mul_norm_sub_sq {a b : ℝ} (hab : a + b ≠ 0) (x y : F) :
    a * ‖y‖ ^ 2 + b * ‖x - y‖ ^ 2 =
      (a + b) * ‖y - (b / (a + b)) • x‖ ^ 2 + a * b / (a + b) * ‖x‖ ^ 2 := by
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    real_inner_smul_right, real_inner_comm]
  field_simp
  ring

/-- **Completing the square** for `‖y‖² / 2 + ‖x - y‖² / (2τ)`: if `τ ≠ 0` and `1 + τ ≠ 0`, it is
`‖x‖² / (2 (1 + τ))` plus `(1 + τ) / (2τ)` times the squared distance from `y` to
`x / (1 + τ)`. -/
theorem norm_sq_div_two_add_norm_sub_sq_div {τ : ℝ} (hτ : τ ≠ 0) (hτ' : 1 + τ ≠ 0) (x y : F) :
    ‖y‖ ^ 2 / 2 + ‖x - y‖ ^ 2 / (2 * τ) =
      ‖x‖ ^ 2 / (2 * (1 + τ)) + (1 + τ) / (2 * τ) * ‖y - (1 + τ)⁻¹ • x‖ ^ 2 := by
  have h₀ : 1 / 2 + 1 / (2 * τ) = (1 + τ) / (2 * τ) := by field_simp; ring
  have h := mul_norm_sq_add_mul_norm_sub_sq (a := 1 / 2) (b := 1 / (2 * τ))
    (h₀ ▸ div_ne_zero hτ' (mul_ne_zero two_ne_zero hτ)) x y
  have h₁ : 1 / (2 * τ) / (1 / 2 + 1 / (2 * τ)) = (1 + τ)⁻¹ := by rw [h₀]; field_simp
  have h₂ : 1 / 2 * (1 / (2 * τ)) / (1 / 2 + 1 / (2 * τ)) = 1 / (2 * (1 + τ)) := by
    rw [h₀]; field_simp
  rw [h₁, h₂, h₀] at h
  linear_combination h

/-- The completed square at the weights `1 - t` and `t`, for extended distances: for `t ∈ [0, 1]`,
`d(x, (1 - t) a + t b) ^ 2 + t (1 - t) d(a, b) ^ 2 = (1 - t) d(x, a) ^ 2 + t d(x, b) ^ 2`. -/
theorem edist_smul_add_smul_sq_add {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (x a b : F) :
    edist x ((1 - t) • a + t • b) ^ 2 + ENNReal.ofReal (t * (1 - t)) * edist a b ^ 2 =
      ENNReal.ofReal (1 - t) * edist x a ^ 2 + ENNReal.ofReal t * edist x b ^ 2 := by
  have h₀ : 0 ≤ t := ht.1
  have h₁ : 0 ≤ 1 - t := sub_nonneg.2 ht.2
  -- The point at which `mul_norm_sq_add_mul_norm_sub_sq` measures the distance from `x`.
  have hcomb : x - a - t • (b - a) = x - ((1 - t) • a + t • b) := by module
  have key := mul_norm_sq_add_mul_norm_sub_sq (a := 1 - t) (b := t) (by simp) (b - a) (x - a)
  rw [sub_add_cancel, one_mul, div_one, div_one, sub_sub_sub_cancel_right, norm_sub_rev b x,
    norm_sub_rev b a, hcomb] at key
  simp only [edist_dist, dist_eq_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [← ENNReal.ofReal_mul (mul_nonneg h₀ h₁), ← ENNReal.ofReal_mul h₁, ← ENNReal.ofReal_mul h₀,
    ← ENNReal.ofReal_add (by positivity) (mul_nonneg (mul_nonneg h₀ h₁) (by positivity)),
    ← ENNReal.ofReal_add (mul_nonneg h₁ (by positivity)) (mul_nonneg h₀ (by positivity))]
  congr 1
  linarith

end TauCeti
