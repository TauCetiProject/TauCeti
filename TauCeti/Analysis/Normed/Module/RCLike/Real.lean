/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.RCLike.Real

import TauCeti.Analysis.Normed.Ring.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Norms of combinations with coefficients in `[0, 1]`

For `x, y ∈ [0, 1]` and vectors `a`, `b` in a real normed space,
`‖x • b + y • a‖ + ‖(1 - y) • a + (1 - x) • b‖ ≤ ‖a‖ + ‖b‖`. The two vectors on the left are the
derivatives of the product `u v` and of `u + v - u v` at a point where `u = x`, `v = y`, `Du = a`
and `Dv = b`, so this is the pointwise inequality behind the submodularity of the perimeter.

Replacing the factors `a` and `b` of the inclusion-exclusion expression `a + b - a b` by `a'` and
`b'` changes it by at most the sum of the two changes when `a'` and `b` lie in `[0, 1]`
(`TauCeti.enorm_add_sub_mul_sub_le_of_mem_Icc`). The corresponding bound for the product `a b`
holds in any seminormed ring: it is `TauCeti.enorm_mul_sub_mul_le`.

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

/-- For `a'` and `b` in `[0, 1]`, replacing the factors `a` and `b` of the inclusion-exclusion
expression `a + b - a b` by `a'` and `b'` changes it by at most the sum of the two changes. -/
theorem enorm_add_sub_mul_sub_le_of_mem_Icc {a a' b b' : ℝ} (ha' : a' ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) :
    ‖(a' + b' - a' * b') - (a + b - a * b)‖ₑ ≤ ‖a' - a‖ₑ + ‖b' - b‖ₑ := by
  -- As `x + y - x y = 1 - (1 - x) (1 - y)`, this is the product bound for `1 - a` and `1 - b`.
  have h := enorm_mul_sub_mul_le (a := 1 - a) (b := 1 - a') (c := 1 - b) (d := 1 - b')
    (by rw [Real.norm_of_nonneg (sub_nonneg.2 ha'.2)]; linarith [ha'.1])
    (by rw [Real.norm_of_nonneg (sub_nonneg.2 hb.2)]; linarith [hb.1])
  rwa [sub_sub_sub_cancel_left, sub_sub_sub_cancel_left,
    show (1 - a) * (1 - b) - (1 - a') * (1 - b') = (a' + b' - a' * b') - (a + b - a * b) by ring]
    at h

end TauCeti
