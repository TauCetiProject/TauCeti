/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The determinant of the pencil `S⁻¹ - X`

For an invertible square matrix `S` over a commutative ring and any `X`, the determinant of the
pencil `S⁻¹ - X` is expressible in `S` and `X` themselves: multiplying through by `det S` clears
the inverse, and Sylvester's determinant identity turns what is left into `det (1 - X * S)`. The
determinant of the inverse pencil follows, with `Ring.inverse` on both sides, so no invertibility
of the pencil is needed.

Nothing here needs an order or a norm on the ring. Taking `X` to be a scaled matrix `c • Θ` gives
the scale form of the matrix pencil carried by an exponential weight
`exp (-trace ((S⁻¹ - c • Θ) * A) / 2)`, where `S` is a scale matrix and `c • Θ` the tilt of a trace
statistic; the positivity of that form, which does need an order, is in
`TauCeti/Analysis/Matrix/Sqrt.lean`.

## Main results

* `Matrix.det_mul_det_inv_sub` — the determinant of the pencil, in the parameters `S` and `X`;
* `Matrix.det_nonsing_inv_inv_sub` — the determinant of the inverse pencil.
-/

public section

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] {S : Matrix ι ι R}

/-- The determinant of the pencil `S⁻¹ - X`, in the parameters `S` and `X` themselves.
Only the invertibility of `S` is used. -/
theorem det_mul_det_inv_sub (hS : IsUnit S.det) (X : Matrix ι ι R) :
    S.det * (S⁻¹ - X).det = (1 - X * S).det := by
  rw [← det_mul, mul_sub, mul_nonsing_inv _ hS, det_one_sub_mul_comm]

/-- The determinant of the inverse pencil `(S⁻¹ - X)⁻¹`. When the pencil is singular both sides
vanish, so only the invertibility of `S` is assumed. -/
theorem det_nonsing_inv_inv_sub (hS : IsUnit S.det) (X : Matrix ι ι R) :
    ((S⁻¹ - X)⁻¹).det = S.det * Ring.inverse (1 - X * S).det := by
  rw [det_nonsing_inv, ← det_mul_det_inv_sub hS X, Ring.mul_inverse_rev, mul_left_comm,
    Ring.mul_inverse_cancel _ hS, mul_one]

end Matrix
