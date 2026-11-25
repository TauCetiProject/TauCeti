/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basis
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.LinearAlgebra.Matrix.Nonsingular

/-!
# Full polarization and the matrix of a quadratic form

The matrix `Q.toMatrix b` uses the half-polarization, so its diagonal coefficients are the
quadratic coefficients. The matrix of the full polarization is twice this matrix. Its determinant
therefore differs from the quadratic discriminant by `2` to the dimension, including dimension
zero. These formulas make the convention explicit when changing between bilinear and quadratic
Gram determinants.

For a nondegenerate quadratic form on a finite coordinate space `ι → R` over a commutative ring in
which `2` is invertible, the polar bilinear form is nondegenerate, so its standard Gram matrix is
right-separating and therefore has non-zerodivisor determinant
(`QuadraticMap.det_toMatrix'_polarBilin_mem_nonZeroDivisors`).

Without `2` invertible, a quadratic form `q` is still `x ↦ xᵀ M x` in the coordinates of a basis
`b` indexed by a linearly ordered type, for its upper triangular *coefficient matrix* `M`
(`QuadraticForm.coefficientMatrix`): the diagonal entries are the values `q(bᵢ)`, the entries above
the diagonal are the polar values `q(bᵢ + bⱼ) - q(bᵢ) - q(bⱼ)`, and the entries below it are `0`
(`QuadraticForm.coefficientMatrix_apply`). For a form on `R^ι`, reading `M` in an `R`-algebra `A`
gives the form `q_A` on `A^ι` with the same coefficients (`QuadraticForm.baseChangeForm`).
Mathlib's `QuadraticForm.baseChange` instead lives on `A ⊗[R] R^ι` and assumes `2` invertible.

## Main declarations

* `QuadraticForm.toMatrix_polarBilin` and `QuadraticForm.det_toMatrix_polarBilin`: the full
  polar matrix and its determinant.
* `QuadraticMap.det_toMatrix'_polarBilin_mem_nonZeroDivisors`: non-zerodivisor determinant of the
  standard polar Gram matrix for nondegenerate `Q`.
* `QuadraticForm.coefficientMatrix` and `QuadraticForm.coefficientMatrix_apply`: the upper
  triangular coefficient matrix of a quadratic form in an ordered basis.
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

namespace QuadraticMap

open scoped nonZeroDivisors

/-- For a nondegenerate quadratic form on `ι → R` over a commutative ring in which `2` is
invertible, the determinant of its standard polar Gram matrix is a non-zerodivisor. -/
theorem det_toMatrix'_polarBilin_mem_nonZeroDivisors
    {R ι : Type*} [CommRing R] [Invertible (2 : R)] [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm R (ι → R)) (hQ : Q.Nondegenerate) :
    (LinearMap.BilinForm.toMatrix' Q.polarBilin).det ∈ R⁰ := by
  have hpolar : Q.polarBilin.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mpr hQ
  have hM : (LinearMap.BilinForm.toMatrix' Q.polarBilin).Nondegenerate :=
    LinearMap.BilinForm.Nondegenerate.toMatrix' hpolar
  rw [← Matrix.nonsingular_iff_det_mem_nonZeroDivisors, ← Matrix.isLeftRegular_iff_nonsingular,
    Matrix.isLeftRegular_iff_mulVec_injective, ← Matrix.coe_mulVecLin, ← LinearMap.ker_eq_bot,
    Matrix.ker_mulVecLin_eq_bot_iff]
  exact fun x hx ↦ hM.separatingRight.eq_zero_of_mulVec_eq_zero hx

end QuadraticMap

open scoped Matrix

namespace QuadraticForm

section Coefficients

variable {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V] [Fintype ι] [LinearOrder ι]

/-- The **coefficient matrix** of a quadratic form `q` in a basis `b` indexed by a linearly ordered
type: the upper triangular matrix `M` with `q(Σ xᵢ bᵢ) = xᵀ M x`, from Mathlib's
`QuadraticMap.toBilin`. -/
noncomputable def coefficientMatrix (q : QuadraticForm R V) (b : Module.Basis ι R V) :
    Matrix ι ι R :=
  LinearMap.toMatrix₂ b b (q.toBilin b)

/-- The entries of the coefficient matrix: `q(bᵢ)` on the diagonal, the polar value
`q(bᵢ + bⱼ) - q(bᵢ) - q(bⱼ)` above it and `0` below it. -/
theorem coefficientMatrix_apply (q : QuadraticForm R V) (b : Module.Basis ι R V) (i j : ι) :
    coefficientMatrix q b i j =
      if i = j then q (b i) else if i < j then QuadraticMap.polar q (b i) (b j) else 0 := by
  rw [coefficientMatrix, LinearMap.toMatrix₂_apply, QuadraticMap.toBilin_apply]

/-- The form `q_A` on `A^ι` with the same coefficients as a form `q` on `R^ι`: `x ↦ xᵀ M x` for
the coefficient matrix `M` of `q` in the standard basis, read in `A`. -/
noncomputable def baseChangeForm (q : QuadraticForm R (ι → R)) (A : Type*) [CommRing A]
    [Algebra R A] : QuadraticForm A (ι → A) :=
  Matrix.toQuadraticForm' ((coefficientMatrix q (Pi.basisFun R ι)).map (algebraMap R A))

/-- The form `q_A` evaluates as `xᵀ M x`. -/
@[simp]
theorem baseChangeForm_apply (q : QuadraticForm R (ι → R)) (A : Type*) [CommRing A]
    [Algebra R A] (x : ι → A) :
    baseChangeForm q A x =
      x ⬝ᵥ ((coefficientMatrix q (Pi.basisFun R ι)).map (algebraMap R A) *ᵥ x) := by
  rw [baseChangeForm, Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply']

/-- Over `R` itself, the form with the coefficients of `q` is `q`. -/
@[simp]
theorem baseChangeForm_self (q : QuadraticForm R (ι → R)) : baseChangeForm q R = q := by
  simp only [baseChangeForm, coefficientMatrix, Algebra.algebraMap_self, RingHom.coe_id,
    Matrix.map_id, Matrix.toQuadraticForm', LinearMap.toMatrix₂_basisFun,
    Matrix.toLinearMap₂'_toMatrix', QuadraticMap.toQuadraticMap_toBilin]

end Coefficients

end QuadraticForm
