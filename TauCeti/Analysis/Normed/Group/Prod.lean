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
`Prod.min_mul_norm_sq_le_add` bounds a weighted sum of squared coordinate norms below by
`min a b * ‖x‖²`, provided at least one coefficient is nonnegative. The other coefficient
may be negative, allowing the estimate to apply to quadratic forms with a signed mass term.
`Prod.norm_mul_self_le_sq_add_sq_add_sq` bounds the squared sup norm on `ℝ³` by the sum of the
squares of the coordinates.
-/

public section

/-- A weighted sum of squared coordinate norms bounds the squared product norm below with
coefficient `min a b`, provided at least one coefficient is nonnegative. -/
theorem _root_.Prod.min_mul_norm_sq_le_add {E F : Type*}
    [SeminormedAddGroup E] [SeminormedAddGroup F] (x : E × F) {a b : ℝ}
    (h : 0 ≤ max a b) :
    min a b * ‖x‖ ^ 2 ≤ a * ‖x.1‖ ^ 2 + b * ‖x.2‖ ^ 2 := by
  by_cases ha : 0 ≤ a
  · by_cases hb : 0 ≤ b
    · rw [Prod.norm_def]
      rcases le_total ‖x.1‖ ‖x.2‖ with hx | hx
      · rw [max_eq_right hx]
        exact (mul_le_mul_of_nonneg_right (min_le_right a b) (sq_nonneg _)).trans
          (le_add_of_nonneg_left (mul_nonneg ha (sq_nonneg _)))
      · rw [max_eq_left hx]
        exact (mul_le_mul_of_nonneg_right (min_le_left a b) (sq_nonneg _)).trans
          (le_add_of_nonneg_right (mul_nonneg hb (sq_nonneg _)))
    · have hb' : b ≤ 0 := le_of_not_ge hb
      rw [min_eq_right (hb'.trans ha)]
      have hsq : ‖x.2‖ ^ 2 ≤ ‖x‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_snd_le x) 2
      exact (mul_le_mul_of_nonpos_left hsq hb').trans
        (le_add_of_nonneg_left (mul_nonneg ha (sq_nonneg _)))
  · have hb : 0 ≤ b := (le_max_iff.mp h).resolve_left ha
    have ha' : a ≤ 0 := le_of_not_ge ha
    rw [min_eq_left (ha'.trans hb)]
    have hsq : ‖x.1‖ ^ 2 ≤ ‖x‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_fst_le x) 2
    exact (mul_le_mul_of_nonpos_left hsq ha').trans
      (le_add_of_nonneg_right (mul_nonneg hb (sq_nonneg _)))

/-- The square of the sup norm on `ℝ³` is at most the sum of the squares of the coordinates. -/
theorem _root_.Prod.norm_mul_self_le_sq_add_sq_add_sq (v : ℝ × ℝ × ℝ) :
    ‖v‖ * ‖v‖ ≤ v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 := by
  have hv : ‖v‖ ≤ √(v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2) := by
    refine norm_prod_le_iff.2 ⟨?_, norm_prod_le_iff.2 ⟨?_, ?_⟩⟩ <;>
      refine Real.abs_le_sqrt ?_ <;> nlinarith [sq_nonneg v.1, sq_nonneg v.2.1, sq_nonneg v.2.2]
  exact (mul_self_le_mul_self (norm_nonneg v) hv).trans (Real.mul_self_sqrt (by positivity)).le
