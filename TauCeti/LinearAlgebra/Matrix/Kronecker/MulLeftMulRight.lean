/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Kronecker
import TauCeti.LinearAlgebra.Matrix.StdBasis

/-!
# The determinant of `X ↦ A * X * B`

On the square matrices `Matrix n n R` over a commutative ring, the `R`-linear map
`X ↦ A * X * B` has the Kronecker product `A ⊗ₖ Bᵀ` as its matrix in the standard basis
(`Matrix.toMatrix_stdBasis_mulLeft_comp_mulRight`), so its determinant is
`det A ^ n * det B ^ n` (`Matrix.det_mulLeft_comp_mulRight`). For `B = Aᴴ` this computes the
determinant of the congruence action of `GL_n` on matrices.
-/

public section

open scoped Kronecker Matrix

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- In the standard basis of `n × n` matrices, the `R`-linear map `X ↦ A * X * B` has the
Kronecker product `A ⊗ₖ Bᵀ` as its matrix. -/
theorem toMatrix_stdBasis_mulLeft_comp_mulRight (A B : Matrix n n R) :
    LinearMap.toMatrix (stdBasis R n n) (stdBasis R n n)
      (LinearMap.mulLeft R A ∘ₗ LinearMap.mulRight R B) = A ⊗ₖ Bᵀ := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [LinearMap.toMatrix_apply, stdBasis_eq_single, Matrix.mul_apply,
    Matrix.single_apply, ite_and, Finset.sum_ite_eq]

/-- **The determinant of two-sided multiplication**: the `R`-linear map `X ↦ A * X * B` on
`n × n` matrices has determinant `det A ^ n * det B ^ n`. -/
theorem det_mulLeft_comp_mulRight (A B : Matrix n n R) :
    LinearMap.det (LinearMap.mulLeft R A ∘ₗ LinearMap.mulRight R B) =
      A.det ^ Fintype.card n * B.det ^ Fintype.card n := by
  rw [← LinearMap.det_toMatrix (stdBasis R n n), toMatrix_stdBasis_mulLeft_comp_mulRight,
    det_kronecker, det_transpose]

end Matrix
