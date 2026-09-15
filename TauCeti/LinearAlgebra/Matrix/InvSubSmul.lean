/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The determinant of the pencil `S⁻¹ - c • Θ`

For an invertible square matrix `S` over a commutative ring and any `Θ` and any scalar `c`, the
determinant of the pencil `S⁻¹ - c • Θ` is expressible in `S` and `Θ` themselves: multiplying
through by `det S` clears the inverse, and Sylvester's determinant identity turns what is left
into `det (1 - c • (Θ * S))`. The determinant of the inverse pencil follows, once the pencil is
itself invertible.

Nothing here needs an order or a norm on the ring. The pencil is the scale form of the matrix
pencil carried by an exponential weight `exp (-trace ((S⁻¹ - c • Θ) * A) / 2)`, where `S` is a
scale matrix and `c • Θ` the tilt of a trace statistic; the positivity of that form, which does
need an order, is in `TauCeti/Analysis/Matrix/Sqrt.lean`.

## Main results

* `Matrix.det_mul_det_inv_sub_smul` — the determinant of the pencil, in the parameters `S` and `Θ`;
* `Matrix.det_nonsing_inv_inv_sub_smul` — the determinant of the inverse pencil.
-/

public section

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] {S : Matrix ι ι R}

/-- The determinant of the scale pencil `S⁻¹ - c • Θ`, in the parameters `S` and `Θ` themselves.
Only the invertibility of `S` is used. -/
theorem det_mul_det_inv_sub_smul (hS : IsUnit S.det) (Θ : Matrix ι ι R) (c : R) :
    S.det * (S⁻¹ - c • Θ).det = (1 - c • (Θ * S)).det := by
  rw [← Matrix.det_mul, Matrix.mul_sub, Matrix.mul_nonsing_inv _ hS, Matrix.mul_smul,
    ← Matrix.smul_mul, Matrix.det_one_sub_mul_comm, Matrix.mul_smul]

/-- The determinant of the inverse scale pencil. This is the determinant of the scale matrix
carried by an exponential weight `exp (-trace ((S⁻¹ - c • Θ) * A) / 2)`. -/
theorem det_nonsing_inv_inv_sub_smul (hS : IsUnit S.det) {Θ : Matrix ι ι R} {c : R}
    (hc : IsUnit (S⁻¹ - c • Θ).det) :
    ((S⁻¹ - c • Θ)⁻¹).det = S.det * Ring.inverse (1 - c • (Θ * S)).det := by
  have hpencil : IsUnit (1 - c • (Θ * S)).det := by
    rw [← det_mul_det_inv_sub_smul hS Θ c]
    exact hS.mul hc
  rw [Matrix.det_nonsing_inv, Ring.eq_mul_inverse_iff_mul_eq _ _ _ hpencil,
    ← det_mul_det_inv_sub_smul hS Θ c, mul_left_comm, Ring.inverse_mul_cancel _ hc, mul_one]

end Matrix
