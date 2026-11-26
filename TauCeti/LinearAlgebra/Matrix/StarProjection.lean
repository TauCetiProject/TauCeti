/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Matrix star projections

A matrix projection is a square matrix `p` over a star ring with `p * p = p` and `pᴴ = p`. This
file records facts about matrix projections that do not depend on comparing projections.
Applying a star ring homomorphism to the entries of a matrix projection gives a matrix projection.
If `a` is self-adjoint and `a * b = 0`, then rectangular matrices whose columns lie in the ranges
of `a` and `b` are orthogonal: `vᴴ * w = 0`, and likewise for rows.
Over a star-ordered proper star ring, such as `ℂ` or a C⋆-algebra with its spectral order,
`vᴴ * v = 0` forces `v = 0` for rectangular matrices (`Matrix.conjTranspose_mul_self_eq_zero`).
Hence a rectangular matrix `v` whose initial element `vᴴ * v` is a projection is a partial
isometry, `v * vᴴ * v = v`.

## Main statements

* `IsStarProjection.matrix_map`: the entrywise image of a matrix projection under a star ring
  homomorphism is a matrix projection.
* `Matrix.conjTranspose_mul_eq_zero_of_mul_eq_zero` and
  `Matrix.mul_conjTranspose_eq_zero_of_mul_eq_zero`: if `a * b = 0` and `a` (respectively `b`)
  is self-adjoint, then rectangular matrices with columns (respectively rows) in the ranges of
  `a` and `b` are orthogonal.
* `IsStarProjection.diag_nonneg`: over a star-ordered ring, the diagonal entries of a matrix
  projection are nonnegative.
* `Matrix.mul_conjTranspose_mul_self_eq_of_isStarProjection`: over a star-ordered proper star
  ring, a matrix `v` with `vᴴ * v` a projection is a partial isometry.
-/

public section

namespace Matrix

variable {m n R : Type*} [Fintype m] [Fintype n]

/-- The entrywise image of a matrix projection under a star ring homomorphism is a matrix
projection. -/
theorem _root_.IsStarProjection.matrix_map {S F : Type*} [NonUnitalNonAssocSemiring R] [Star R]
    [NonUnitalNonAssocSemiring S] [Star S] [FunLike F R S] [NonUnitalRingHomClass F R S]
    [StarHomClass F R S] {p : Matrix m m R} (hp : IsStarProjection p) (f : F) :
    IsStarProjection (p.map f) :=
  ⟨by rw [IsIdempotentElem, ← Matrix.map_mul, hp.isIdempotentElem.eq],
    (IsHermitian.map hp.isSelfAdjoint f fun _ ↦ map_star f _).isSelfAdjoint⟩

section NonUnitalSemiring

variable [NonUnitalSemiring R] [StarRing R]

/-- If `a` is self-adjoint and `a * b = 0`, then matrices `v` and `w` with `a * v = v` and
`b * w = w` (columns in the ranges of `a` and `b`) satisfy `vᴴ * w = 0`. -/
theorem conjTranspose_mul_eq_zero_of_mul_eq_zero {k l : Type*} {a b : Matrix n n R}
    (ha : IsSelfAdjoint a) {v : Matrix n k R} {w : Matrix n l R} (hv : a * v = v)
    (hw : b * w = w) (hab : a * b = 0) : vᴴ * w = 0 := by
  rw [← hv, ← hw, conjTranspose_mul, ← star_eq_conjTranspose a, ha.star_eq, Matrix.mul_assoc,
    ← Matrix.mul_assoc a, hab, Matrix.zero_mul, Matrix.mul_zero]

/-- If `b` is self-adjoint and `a * b = 0`, then matrices `v` and `w` with `v * a = v` and
`w * b = w` (rows in the ranges of `a` and `b`) satisfy `v * wᴴ = 0`. -/
theorem mul_conjTranspose_eq_zero_of_mul_eq_zero {k l : Type*} {a b : Matrix m m R}
    (hb : IsSelfAdjoint b) {v : Matrix k m R} {w : Matrix l m R} (hv : v * a = v)
    (hw : w * b = w) (hab : a * b = 0) : v * wᴴ = 0 := by
  rw [← hv, ← hw, conjTranspose_mul, ← star_eq_conjTranspose b, hb.star_eq, ← Matrix.mul_assoc,
    Matrix.mul_assoc v, hab, Matrix.mul_zero, Matrix.zero_mul]

end NonUnitalSemiring

/-- Over a star-ordered ring, the diagonal entries of a matrix projection are nonnegative. -/
theorem _root_.IsStarProjection.diag_nonneg [NonUnitalSemiring R] [PartialOrder R] [StarRing R]
    [StarOrderedRing R] {p : Matrix m m R} (hp : IsStarProjection p) (i : m) : 0 ≤ p i i := by
  have h : pᴴ * p = p := by
    rw [← star_eq_conjTranspose, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
  rw [← h, Matrix.mul_apply]
  exact Finset.sum_nonneg fun k _ ↦ by simp

section StarOrderedRing

variable [NonUnitalRing R] [StarRing R] [PartialOrder R] [StarOrderedRing R] [IsProperStar R]

/-- Over a star-ordered proper star ring, a rectangular matrix `v` whose initial element `vᴴ * v` is
a projection is a partial isometry. -/
theorem mul_conjTranspose_mul_self_eq_of_isStarProjection {v : Matrix n m R}
    (h : IsStarProjection (vᴴ * v)) : v * vᴴ * v = v := by
  have hp : vᴴ * (v * (vᴴ * v)) = vᴴ * v := by
    rw [← Matrix.mul_assoc, h.isIdempotentElem.eq]
  have hx : (v * (vᴴ * v) - v)ᴴ * (v * (vᴴ * v) - v) = 0 := by
    simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.sub_mul,
      Matrix.mul_sub, Matrix.mul_assoc, hp, sub_self]
  rw [conjTranspose_mul_self_eq_zero, sub_eq_zero] at hx
  rwa [Matrix.mul_assoc]

end StarOrderedRing

end Matrix
