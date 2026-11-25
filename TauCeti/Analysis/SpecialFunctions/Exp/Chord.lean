/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The chord of the real exponential

By convexity, the real exponential lies below its chord over an interval.

## Main statements

* `Real.exp_mul_le_add_mul`: for `x ∈ [a, b]` with `a < b`, `exp (t * x)` is at most the value at
  `x` of the chord of `s ↦ exp (t * s)` through the points `a` and `b`.
* `Real.exp_mul_sub_one_lt_div_mul`: for `b ≠ 0` and `0 < t < s`,
  `exp (b t) − 1 < (t / s) (exp (b s) − 1)`, by strict convexity.
-/

public section

namespace Real

/-- The chord of the exponential lies above it on `[a, b]`. -/
theorem exp_mul_le_add_mul {a b x : ℝ} (hab : a < b) (hx : x ∈ Set.Icc a b) (t : ℝ) :
    exp (t * x) ≤ (b * exp (t * a) - a * exp (t * b)) / (b - a) +
      (exp (t * b) - exp (t * a)) / (b - a) * x := by
  have hba : 0 < b - a := sub_pos.2 hab
  have hconv := convexOn_exp.2 (Set.mem_univ (t * a)) (Set.mem_univ (t * b))
    (div_nonneg (sub_nonneg.2 hx.2) hba.le) (div_nonneg (sub_nonneg.2 hx.1) hba.le)
    (by field_simp; ring)
  simp only [smul_eq_mul] at hconv
  have h1 : (b - x) / (b - a) * (t * a) + (x - a) / (b - a) * (t * b) = t * x := by
    field_simp; ring
  rw [h1] at hconv
  refine hconv.trans_eq ?_
  field_simp; ring

/-- Strict convexity of the exponential along a chord from `0`: for `b ≠ 0` and `0 < t < s`,
`exp (b t) − 1 < (t / s) (exp (b s) − 1)`. -/
theorem exp_mul_sub_one_lt_div_mul {b t s : ℝ} (hb : b ≠ 0) (ht : 0 < t) (hts : t < s) :
    exp (b * t) - 1 < t / s * (exp (b * s) - 1) := by
  have hs : 0 < s := ht.trans hts
  have hθ0 : 0 < t / s := div_pos ht hs
  have hθ1 : t / s < 1 := (div_lt_one hs).mpr hts
  have h := strictConvexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ (b * s))
    (mul_ne_zero hb hs.ne').symm (by linarith : 0 < 1 - t / s) hθ0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, exp_zero, mul_one] at h
  rw [show t / s * (b * s) = b * t by field_simp] at h
  linarith

end Real
