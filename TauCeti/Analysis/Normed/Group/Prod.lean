/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real

import Mathlib.Analysis.Real.Sqrt

/-!
# Weighted lower bounds for the product norm

The norm on a product of seminormed groups is the maximum of the coordinate norms.
`Prod.min_mul_norm_pow_le_add` bounds a weighted sum of `n`-th powers of coordinate norms below
by `min a b * ‖x‖ ^ n`, provided at least one coefficient is nonnegative. The other coefficient
may be negative, allowing the estimate to apply to quadratic forms with a signed mass term.
`Prod.norm_mul_self_le_sq_add_sq_add_sq` bounds the squared sup norm on `ℝ³` by the sum of the
squares of the coordinates.
-/

public section

/-- A weighted sum of `n`-th powers of coordinate norms bounds the `n`-th power of the product
norm below with coefficient `min a b`, provided at least one coefficient is nonnegative. -/
theorem Prod.min_mul_norm_pow_le_add {E F : Type*} [SeminormedAddGroup E] [SeminormedAddGroup F]
    (x : E × F) (n : ℕ) {a b : ℝ} (h : 0 ≤ max a b) :
    min a b * ‖x‖ ^ n ≤ a * ‖x.1‖ ^ n + b * ‖x.2‖ ^ n := by
  have hs := pow_nonneg (norm_nonneg x.1) n
  have ht := pow_nonneg (norm_nonneg x.2) n
  rcases le_total a b with hab | hab <;> rcases le_total ‖x.1‖ ‖x.2‖ with hx | hx <;>
    simp only [Prod.norm_def, min_eq_left, min_eq_right, max_eq_left, max_eq_right, hab, hx]
      at h ⊢ <;>
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) hx n]

/-- The square of the sup norm on `ℝ³` is at most the sum of the squares of the coordinates. -/
theorem Prod.norm_mul_self_le_sq_add_sq_add_sq (v : ℝ × ℝ × ℝ) :
    ‖v‖ * ‖v‖ ≤ v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 := by
  have hv : ‖v‖ ≤ √(v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2) := by
    refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩ <;>
      refine Real.abs_le_sqrt ?_ <;> nlinarith [sq_nonneg v.1, sq_nonneg v.2.1, sq_nonneg v.2.2]
  exact (mul_self_le_mul_self (norm_nonneg v) hv).trans (Real.mul_self_sqrt (by positivity)).le
