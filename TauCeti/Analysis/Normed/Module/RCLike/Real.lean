/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.RCLike.Real

import TauCeti.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Norms of combinations with coefficients in `[0, 1]`

For `x, y ∈ [0, 1]` and vectors `a`, `b` in a real normed space,
`‖x • b + y • a‖ + ‖(1 - y) • a + (1 - x) • b‖ ≤ ‖a‖ + ‖b‖`. The two vectors on the left are the
derivatives of the product `u v` and of `u + v - u v` at a point where `u = x`, `v = y`, `Du = a`
and `Dv = b`, so this is the pointwise inequality behind the submodularity of the perimeter.

Replacing the factors `a` and `b` of a product, or of the inclusion-exclusion expression
`a + b - a b`, by `a'` and `b'` in `[0, 1]` changes it by at most the sum of the two changes.

Half the difference of two vectors has at most half their distance as its norm.
-/

public section

namespace TauCeti

open Set

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- Half the difference of two points at distance at most `d` has norm at most `d / 2`. -/
theorem norm_half_smul_sub_le {a b : E} {d : ℝ} (h : ‖a - b‖ ≤ d) :
    ‖(1 / 2 : ℝ) • (a - b)‖ ≤ d / 2 := by
  rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
  linarith

/-- For `x, y ∈ [0, 1]`, the vectors `x • b + y • a` and `(1 - y) • a + (1 - x) • b` have total
norm at most `‖a‖ + ‖b‖`. -/
theorem norm_smul_add_add_norm_smul_add_le {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) (a b : E) :
    ‖x • b + y • a‖ + ‖(1 - y) • a + (1 - x) • b‖ ≤ ‖a‖ + ‖b‖ := by
  have h₁ := norm_add_le (x • b) (y • a)
  have h₂ := norm_add_le ((1 - y) • a) ((1 - x) • b)
  rw [norm_smul_of_nonneg hx.1, norm_smul_of_nonneg hy.1] at h₁
  rw [norm_smul_of_nonneg (sub_nonneg.2 hy.2), norm_smul_of_nonneg (sub_nonneg.2 hx.2)] at h₂
  linarith

/-- Replacing the factors `a` and `b` in `[0, 1]` by `a'` and `b'` in `[0, 1]` changes the product
by at most the sum of the two changes. -/
theorem enorm_mul_sub_mul_le_of_mem_Icc {a a' b b' : ℝ} (ha : a ∈ Icc (0 : ℝ) 1)
    (hb' : b' ∈ Icc (0 : ℝ) 1) : ‖a' * b' - a * b‖ₑ ≤ ‖a' - a‖ₑ + ‖b' - b‖ₑ := by
  simp only [← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (abs_mul_sub_mul_le (abs_le.2 ⟨by linarith [ha.1], ha.2⟩)
    (abs_le.2 ⟨by linarith [hb'.1], hb'.2⟩))

/-- Replacing the factors `a` and `b` in `[0, 1]` by `a'` and `b'` in `[0, 1]` changes `a + b - a b`
by at most the sum of the two changes. -/
theorem enorm_add_sub_mul_sub_le_of_mem_Icc {a a' b b' : ℝ} (ha' : a' ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) :
    ‖(a' + b' - a' * b') - (a + b - a * b)‖ₑ ≤ ‖a' - a‖ₑ + ‖b' - b‖ₑ := by
  have h := enorm_mul_sub_mul_le_of_mem_Icc (a := 1 - a') (a' := 1 - a) (b := 1 - b')
    (b' := 1 - b) ⟨by linarith [ha'.2], by linarith [ha'.1]⟩
    ⟨by linarith [hb.2], by linarith [hb.1]⟩
  rwa [sub_sub_sub_cancel_left, sub_sub_sub_cancel_left,
    show (1 - a) * (1 - b) - (1 - a') * (1 - b') = (a' + b' - a' * b') - (a + b - a * b) by ring]
    at h

end TauCeti
