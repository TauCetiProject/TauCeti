/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
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
  have hinj : Function.Injective (LinearMap.BilinForm.toMatrix' Q.polarBilin).mulVec :=
    fun x y hxy ↦
      sub_eq_zero.mp (hM.separatingRight.eq_zero_of_mulVec_eq_zero
        (by rw [Matrix.mulVec_sub, hxy, sub_self]))
  exact Matrix.nonsingular_iff_det_mem_nonZeroDivisors.mp
    (.of_linearIndependent_col (Matrix.mulVec_injective_iff.mp hinj))

end QuadraticMap
