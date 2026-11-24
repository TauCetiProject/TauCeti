/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Basis
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Full polarization and the matrix of a quadratic form

The matrix `Q.toMatrix b` uses the half-polarization, so its diagonal coefficients are the
quadratic coefficients. The matrix of the full polarization is twice this matrix. Its determinant
therefore differs from the quadratic discriminant by `2` to the dimension, including dimension
zero. These formulas make the convention explicit when changing between bilinear and quadratic
Gram determinants.

Without `2` invertible, a quadratic form `q` on `Rⁿ` is still `x ↦ xᵀ M x` for its upper
triangular *coefficient matrix* `M` (`QuadraticForm.coefficientMatrix`): the diagonal entries
are the values `q(eᵢ)`, the entries above the diagonal are the polar values `q(eᵢ + eⱼ) - q(eᵢ) -
q(eⱼ)`, and the entries below it are `0` (`QuadraticForm.coefficientMatrix_apply`). Reading `M` in
an `R`-algebra `A` gives the form `q_A` on `Aⁿ` with the same coefficients
(`QuadraticForm.baseChangeForm`). Mathlib's `QuadraticForm.baseChange` instead lives on
`A ⊗[R] Rⁿ` and assumes `2` invertible.

## Main declarations

* `QuadraticForm.toMatrix_polarBilin` and `QuadraticForm.det_toMatrix_polarBilin`: the full
  polar matrix and its determinant.
* `QuadraticForm.coefficientMatrix` and `QuadraticForm.coefficientMatrix_apply`: the upper
  triangular coefficient matrix of a quadratic form on `Rⁿ`.
* `QuadraticForm.baseChangeForm`, `QuadraticForm.baseChangeForm_apply` and
  `QuadraticForm.baseChangeForm_self`: the form with the same coefficients over an `R`-algebra.
-/

public section

namespace QuadraticForm

variable {R V ι : Type*} [CommRing R] [Invertible (2 : R)]
  [AddCommGroup V] [Module R V] [Fintype ι] [DecidableEq ι]

/-- The full polar matrix is twice the quadratic Gram matrix. -/
theorem toMatrix_polarBilin (Q : QuadraticForm R V) (b : Module.Basis ι R V) :
    LinearMap.BilinForm.toMatrix b Q.polarBilin = (2 : R) • Q.toMatrix b := by
  ext i j
  rw [LinearMap.BilinForm.toMatrix_apply, Matrix.smul_apply, QuadraticForm.toMatrix,
    LinearMap.toMatrix₂_apply]
  have h := congrArg (fun B : LinearMap.BilinForm R V => B (b i) (b j))
    (QuadraticMap.two_nsmul_associated R Q)
  simpa only [LinearMap.add_apply, two_nsmul, Matrix.smul_apply, smul_eq_mul, two_mul] using h.symm

/-- The determinant of the full polar matrix is `2^dim` times the quadratic discriminant. -/
theorem det_toMatrix_polarBilin (Q : QuadraticForm R V) (b : Module.Basis ι R V) :
    (LinearMap.BilinForm.toMatrix b Q.polarBilin).det =
      (2 : R) ^ Fintype.card ι * Q.discr b := by
  rw [toMatrix_polarBilin, Matrix.det_smul, QuadraticForm.discr]

end QuadraticForm

open scoped Matrix

namespace QuadraticForm

section Coefficients

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The **coefficient matrix** of a quadratic form `q` on `Rⁿ`: the upper triangular matrix `M`
with `q(x) = xᵀ M x`, from Mathlib's `QuadraticMap.toBilin` in the standard basis. -/
noncomputable def coefficientMatrix (q : QuadraticForm R (Fin n → R)) :
    Matrix (Fin n) (Fin n) R :=
  LinearMap.toMatrix₂' R (q.toBilin (Pi.basisFun R (Fin n)))

/-- The entries of the coefficient matrix: `q(eᵢ)` on the diagonal, the polar value
`q(eᵢ + eⱼ) - q(eᵢ) - q(eⱼ)` above it and `0` below it. -/
theorem coefficientMatrix_apply (q : QuadraticForm R (Fin n → R)) (i j : Fin n) :
    coefficientMatrix q i j =
      if i = j then q (Pi.single i 1)
      else if i < j then QuadraticMap.polar q (Pi.single i 1) (Pi.single j 1) else 0 := by
  rw [coefficientMatrix, LinearMap.toMatrix₂'_apply, ← Pi.basisFun_apply R (Fin n) i,
    ← Pi.basisFun_apply R (Fin n) j, QuadraticMap.toBilin_apply]

/-- The form `q_A` on `Aⁿ` with the same coefficients as `q`: `x ↦ xᵀ M x` for the coefficient
matrix `M` of `q` read in `A`. -/
noncomputable def baseChangeForm (q : QuadraticForm R (Fin n → R)) (A : Type*) [CommRing A]
    [Algebra R A] : QuadraticForm A (Fin n → A) :=
  Matrix.toQuadraticForm' ((coefficientMatrix q).map (algebraMap R A))

/-- The form `q_A` evaluates as `xᵀ M x`. -/
theorem baseChangeForm_apply (q : QuadraticForm R (Fin n → R)) (A : Type*) [CommRing A]
    [Algebra R A] (x : Fin n → A) :
    baseChangeForm q A x = x ⬝ᵥ ((coefficientMatrix q).map (algebraMap R A) *ᵥ x) := by
  rw [baseChangeForm, Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply']

/-- Over `R` itself, the form with the coefficients of `q` is `q`. -/
@[simp]
theorem baseChangeForm_self (q : QuadraticForm R (Fin n → R)) : baseChangeForm q R = q := by
  rw [baseChangeForm, Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id, coefficientMatrix,
    Matrix.toQuadraticForm', Matrix.toLinearMap₂'_toMatrix', QuadraticMap.toQuadraticMap_toBilin]

end Coefficients

end QuadraticForm
