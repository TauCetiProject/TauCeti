/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Side lengths of a triangle in a real inner product space

The squared sides of the triangle with vertices `a, b, c` sum to
`3 (‖a‖² + ‖b‖² + ‖c‖²) - ‖a + b + c‖²`. In particular, a triangle inscribed in the sphere of
radius `R` whose centroid is the centre is equilateral, with sides `√3 R`.

## Main results

* `TauCeti.norm_sub_sq_add_norm_sub_sq_add_norm_sub_sq`: the sum of the squared sides of a
  triangle in terms of the norms of its vertices and of their sum.
* `TauCeti.norm_sub_eq_sqrt_three_mul_of_add_add_eq_zero`: three vectors of norm `R` with sum
  zero are pairwise at distance `√3 R`.
-/

public section

open scoped RealInnerProductSpace

namespace TauCeti

variable {F : Type*} [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The sum of the squared sides of the triangle with vertices `a, b, c` is
`3 (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) - ‖a + b + c‖ ^ 2`. -/
theorem norm_sub_sq_add_norm_sub_sq_add_norm_sub_sq (a b c : F) :
    ‖b - a‖ ^ 2 + ‖c - b‖ ^ 2 + ‖a - c‖ ^ 2 =
      3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) - ‖a + b + c‖ ^ 2 := by
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real, norm_add_sq_real, norm_add_sq_real,
    inner_add_left, real_inner_comm a b, real_inner_comm b c]
  ring

/-- Two vertices of a triangle inscribed in the sphere of radius `R`, with centroid at the
centre, are at distance `√3 R`. -/
theorem norm_sub_eq_sqrt_three_mul_of_add_add_eq_zero {R : ℝ} {a b c : F} (ha : ‖a‖ = R)
    (hb : ‖b‖ = R) (hc : ‖c‖ = R) (habc : a + b + c = 0) : ‖b - a‖ = √3 * R := by
  have hR : 0 ≤ R := ha ▸ norm_nonneg a
  have hab : a + b = -c := eq_neg_of_add_eq_zero_left habc
  have h1 := norm_add_sq_real a b
  rw [hab, norm_neg, ha, hb, hc] at h1
  refine (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  rw [norm_sub_sq_real, ha, hb, mul_pow, Real.sq_sqrt (by norm_num), real_inner_comm]
  linarith

end TauCeti
