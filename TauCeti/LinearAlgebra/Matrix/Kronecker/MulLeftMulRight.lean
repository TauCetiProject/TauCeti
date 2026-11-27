/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.StdBasis
import TauCeti.LinearAlgebra.Complex.Determinant

/-!
# The determinant of `X ↦ A * X * B`

On the square matrices `Matrix n n R` over a commutative ring, the `R`-linear map
`X ↦ A * X * B` has the Kronecker product `A ⊗ₖ Bᵀ` as its matrix in the standard basis
(`Matrix.toMatrix_stdBasis_mulLeft_comp_mulRight`), so its determinant is
`det A ^ n * det B ^ n` (`Matrix.det_mulLeft_comp_mulRight`). For `B = Aᴴ` this computes the
determinant of the congruence action of `GL_n` on matrices. In particular, unitary conjugation
has determinant one, including over the real scalars for complex matrices.
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
  have hrepr (X : Matrix n n R) (p : n × n) : (stdBasis R n n).repr X p = X p.1 p.2 := by
    simp [stdBasis]
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [LinearMap.toMatrix_apply, stdBasis_eq_single, hrepr, Matrix.mul_apply,
    Matrix.single_apply, ite_and, Finset.sum_ite_eq]

/-- **The determinant of two-sided multiplication**: the `R`-linear map `X ↦ A * X * B` on
`n × n` matrices has determinant `det A ^ n * det B ^ n`. -/
theorem det_mulLeft_comp_mulRight (A B : Matrix n n R) :
    LinearMap.det (LinearMap.mulLeft R A ∘ₗ LinearMap.mulRight R B) =
      A.det ^ Fintype.card n * B.det ^ Fintype.card n := by
  rw [← LinearMap.det_toMatrix (stdBasis R n n), toMatrix_stdBasis_mulLeft_comp_mulRight,
    det_kronecker, det_transpose]

/-- Two-sided multiplication by inverse matrices has determinant one. -/
theorem det_mulLeft_comp_mulRight_of_mul_eq_one (A B : Matrix n n R) (h : A * B = 1) :
    LinearMap.det (LinearMap.mulLeft R A ∘ₗ LinearMap.mulRight R B) = 1 := by
  rw [det_mulLeft_comp_mulRight, ← mul_pow, ← det_mul, h, det_one, one_pow]

namespace UnitaryGroup

/-- The linear action of a unitary matrix by conjugation on all square matrices has
determinant one. -/
theorem det_conjStarAlgAut [StarRing R] (U : unitaryGroup n R) :
    (Unitary.conjStarAlgAut R _ U).toAlgEquiv.toLinearMap.det = 1 := by
  have h : (Unitary.conjStarAlgAut R _ U).toAlgEquiv.toLinearMap =
      LinearMap.mulLeft R (U : Matrix n n R) ∘ₗ
        LinearMap.mulRight R (star (U : Matrix n n R)) := by
    apply LinearMap.ext
    intro M
    simp [mul_assoc]
  rw [h, det_mulLeft_comp_mulRight_of_mul_eq_one _ _ (Unitary.mul_star_self_of_mem U.property)]

/-- Unitary conjugation of complex matrices has real determinant one. -/
theorem det_conjStarAlgAut_restrictScalars (U : unitaryGroup n ℂ) :
    ((Unitary.conjStarAlgAut ℂ _ U).toAlgEquiv.toLinearMap.restrictScalars ℝ).det = 1 := by
  rw [LinearMap.det_restrictScalars_eq_normSq, det_conjStarAlgAut, Complex.normSq_one]

end UnitaryGroup

end Matrix
