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

end Real
