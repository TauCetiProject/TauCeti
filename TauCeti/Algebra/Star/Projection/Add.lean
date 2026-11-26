/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
import Mathlib.Tactic.Abel

/-!
# Orthogonal summands of star projections

If `e` and `e + y` are idempotents of a ring, then `e y + y e + y y = y`
(`IsIdempotentElem.mul_add_mul_add_mul_eq`). Consequently, if `e`, `e + x` and `e + y` are star
projections with `x y = y x = 0`, then so is `e + x + y`
(`IsStarProjection.add_add_of_mul_eq_zero`).
-/

public section

variable {R : Type*} [NonUnitalRing R] {e x y : R}

/-- If `e` and `e + y` are idempotents, then `e y + y e + y y = y`. -/
theorem IsIdempotentElem.mul_add_mul_add_mul_eq (he : IsIdempotentElem e)
    (hey : IsIdempotentElem (e + y)) : e * y + y * e + y * y = y := by
  have h := hey.eq
  rw [mul_add, add_mul, add_mul, he.eq] at h
  have h' : e + (e * y + y * e + y * y) = e + y := by rw [← h]; abel
  exact add_left_cancel h'

/-- If `e`, `e + x` and `e + y` are star projections and `x y = y x = 0`, then `e + x + y` is a
star projection. -/
theorem IsStarProjection.add_add_of_mul_eq_zero [StarRing R] (he : IsStarProjection e)
    (hex : IsStarProjection (e + x)) (hey : IsStarProjection (e + y)) (hxy : x * y = 0)
    (hyx : y * x = 0) : IsStarProjection (e + x + y) := by
  refine ⟨?_, ?_⟩
  · have hx := he.isIdempotentElem.mul_add_mul_add_mul_eq hex.isIdempotentElem
    have hy := he.isIdempotentElem.mul_add_mul_add_mul_eq hey.isIdempotentElem
    rw [IsIdempotentElem]
    simp only [mul_add, add_mul, hxy, hyx, he.isIdempotentElem.eq, add_zero]
    calc _ = e + (e * x + x * e + x * x) + (e * y + y * e + y * y) := by abel
      _ = e + x + y := by rw [hx, hy]
  · convert (hex.isSelfAdjoint.add hey.isSelfAdjoint).sub he.isSelfAdjoint using 1
    abel
