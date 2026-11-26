/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
import Mathlib.Tactic.Abel
import TauCeti.Algebra.Ring.Idempotent.Basic
import TauCeti.Algebra.Star.SelfAdjoint

/-!
# Orthogonal summands of star projections

If `e`, `e + x` and `e + y` are star projections with `x y = 0`, then so is `e + x + y`
(`IsStarProjection.add_add_of_mul_eq_zero`); since `x` and `y` are self-adjoint, also `y x = 0`.
The idempotent part follows from the identities
`e x + x e + x x = x` and `e y + y e + y y = y` (`IsIdempotentElem.mul_add_mul_add_mul_eq`).
-/

public section

variable {R : Type*} [NonUnitalNonAssocRing R] [StarRing R] {e x y : R}

/-- If `e`, `e + x` and `e + y` are star projections and `x y = 0`, then `e + x + y` is a star
projection. -/
theorem IsStarProjection.add_add_of_mul_eq_zero (he : IsStarProjection e)
    (hex : IsStarProjection (e + x)) (hey : IsStarProjection (e + y)) (hxy : x * y = 0) :
    IsStarProjection (e + x + y) := by
  have hys := hey.isSelfAdjoint.of_add_right he.isSelfAdjoint
  have hyx : y * x = 0 := by
    simpa only [hys.star_eq] using
      (hex.isSelfAdjoint.of_add_right he.isSelfAdjoint).star_mul_eq_zero_of_mul_eq_zero hxy
  refine ⟨?_, hex.isSelfAdjoint.add hys⟩
  have hx := he.isIdempotentElem.mul_add_mul_add_mul_eq hex.isIdempotentElem
  have hy := he.isIdempotentElem.mul_add_mul_add_mul_eq hey.isIdempotentElem
  rw [IsIdempotentElem]
  simp only [mul_add, add_mul, hxy, hyx, he.isIdempotentElem.eq, add_zero]
  calc _ = e + (e * x + x * e + x * x) + (e * y + y * e + y * y) := by abel
    _ = e + x + y := by rw [hx, hy]
