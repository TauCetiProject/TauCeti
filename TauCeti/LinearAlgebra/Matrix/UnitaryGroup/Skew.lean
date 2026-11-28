/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Skew-adjoint coordinates for a hermitian form

For an invertible hermitian Gram matrix `A`, multiplication by `A⁻¹` identifies
skew-hermitian matrices with matrices skew-adjoint for `A`. These coordinates let
one approximate the Lie algebra of a unitary group by projecting arbitrary matrices.
-/

public section

namespace Matrix

variable {n : Type*} [Fintype n]

section Ring

variable {R : Type*} [Ring R] [StarRing R] {A X : Matrix n n R}

/-- For a hermitian Gram matrix `A`, a matrix `X` is skew-adjoint for the form of `A`
exactly when `A * X` is skew-hermitian. -/
theorem star_mul_add_mul_eq_zero_iff (hA : A.IsHermitian) :
    star X * A + A * X = 0 ↔ star (A * X) = -(A * X) := by
  rw [star_mul, star_eq_conjTranspose A, hA.eq, add_eq_zero_iff_eq_neg]

end Ring

variable {R : Type*} [CommRing R] [StarRing R] [DecidableEq n] {A : Matrix n n R}

/-- For hermitian `A`, `A⁻¹ (X - X*)` is skew-adjoint for the form of `A`.
For singular `A`, the totalized inverse is zero. -/
theorem star_inv_mul_sub_star_mul_add (hA : A.IsHermitian)
    (X : Matrix n n R) :
    star (A⁻¹ * (X - star X)) * A + A * (A⁻¹ * (X - star X)) = 0 := by
  by_cases hA' : IsUnit A
  · rw [star_mul_add_mul_eq_zero_iff hA,
      mul_nonsing_inv_cancel_left _ _ ((isUnit_iff_isUnit_det _).1 hA')]
    simp [star_sub]
  · rw [nonsing_inv_apply_not_isUnit A (mt (isUnit_iff_isUnit_det A).2 hA')]
    simp

end Matrix
