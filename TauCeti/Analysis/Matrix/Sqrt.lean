/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Rank
public import TauCeti.Analysis.Matrix.EuclideanLin

/-!
# Sandwiches by the square root of a positive-semidefinite matrix

The continuous-functional-calculus square root `CFC.sqrt S` of a matrix `S` is positive
semidefinite (`CFC.sqrt_nonneg`), hence Hermitian. Sandwiching a Hermitian matrix `Θ` between
two copies of it gives the Hermitian matrix `CFC.sqrt S * Θ * CFC.sqrt S`, whose quadratic form
is the pullback of the quadratic form of `Θ` along `CFC.sqrt S`. For positive-semidefinite `S`,
its pencils `1 - c • (CFC.sqrt S * Θ * CFC.sqrt S)` have the same determinant as those of
`Θ * S`, by Sylvester's determinant identity and `CFC.sqrt S * CFC.sqrt S = S`.

The sandwich is the matrix whose eigenvalues govern the exponential moments of a Gaussian
quadratic form, and the determinant identity is what turns its spectral formula into a formula
in the original parameters.

## Main results

* `Matrix.isHermitian_sqrt_mul_mul_sqrt` — the sandwich of a Hermitian matrix by a square root
  is Hermitian;
* `Matrix.PosSemidef.rank_sqrt` — the square root of a positive-semidefinite matrix has the same
  rank;
* `Matrix.inner_toEuclideanCLM_sqrt_toEuclideanLin` — the quadratic form of `Θ` at
  `CFC.sqrt S x` is the quadratic form of the sandwich at `x`;
* `Matrix.PosSemidef.det_one_sub_smul_sqrt_mul_mul_sqrt_eq_det_one_sub_smul_mul` — for
  positive-semidefinite `S`, the pencil determinants of the sandwich and of `Θ * S` agree.
-/

public section

noncomputable section

open scoped ComplexOrder InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]

open scoped Classical in
/-- The square root of a positive-semidefinite matrix has the same rank as the matrix. -/
@[simp]
theorem PosSemidef.rank_sqrt {S : Matrix ι ι 𝕜} (hS : S.PosSemidef) :
    (CFC.sqrt S).rank = S.rank := by
  have hh : (CFC.sqrt S).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg S)).isHermitian
  have hfac : (CFC.sqrt S)ᴴ * CFC.sqrt S = S := by
    rw [hh.eq, CFC.sqrt_mul_sqrt_self S hS.nonneg]
  conv_rhs => rw [← hfac]
  rw [Matrix.rank_conjTranspose_mul_self]

open scoped Classical in
/-- Sandwiching a Hermitian matrix between two copies of a square root gives a Hermitian
matrix. -/
theorem isHermitian_sqrt_mul_mul_sqrt (S : Matrix ι ι 𝕜) {Θ : Matrix ι ι 𝕜}
    (hΘ : Θ.IsHermitian) : (CFC.sqrt S * Θ * CFC.sqrt S).IsHermitian := by
  simpa only [(Matrix.LE.le.posSemidef (CFC.sqrt_nonneg S)).1.eq] using
    isHermitian_conjTranspose_mul_mul (CFC.sqrt S) hΘ

/-- The quadratic form of `Θ` at `CFC.sqrt S x` is the quadratic form of the sandwich
`CFC.sqrt S * Θ * CFC.sqrt S` at `x`. -/
theorem inner_toEuclideanCLM_sqrt_toEuclideanLin [DecidableEq ι] (S Θ : Matrix ι ι 𝕜)
    (x : EuclideanSpace 𝕜 ι) :
    ⟪toEuclideanCLM (𝕜 := 𝕜) (CFC.sqrt S) x,
        Θ.toEuclideanLin (toEuclideanCLM (𝕜 := 𝕜) (CFC.sqrt S) x)⟫_𝕜 =
      ⟪x, (CFC.sqrt S * Θ * CFC.sqrt S).toEuclideanLin x⟫_𝕜 := by
  simp only [← ContinuousLinearMap.coe_coe, coe_toEuclideanCLM_eq_toEuclideanLin,
    inner_toEuclideanLin_toEuclideanLin, (Matrix.LE.le.posSemidef (CFC.sqrt_nonneg S)).1.eq]

/-- For positive-semidefinite `S`, the pencils of the sandwich `CFC.sqrt S * Θ * CFC.sqrt S` and
of the product `Θ * S` have the same determinant. -/
theorem PosSemidef.det_one_sub_smul_sqrt_mul_mul_sqrt_eq_det_one_sub_smul_mul [DecidableEq ι]
    {S : Matrix ι ι 𝕜} (hS : S.PosSemidef) (Θ : Matrix ι ι 𝕜) (c : 𝕜) :
    (1 - c • (CFC.sqrt S * Θ * CFC.sqrt S)).det = (1 - c • (Θ * S)).det := by
  have hsq : CFC.sqrt S * CFC.sqrt S = S :=
    CFC.sqrt_mul_sqrt_self S hS.nonneg
  rw [← Matrix.smul_mul, det_one_sub_mul_comm, Matrix.mul_smul, ← Matrix.mul_assoc, hsq,
    ← Matrix.smul_mul, det_one_sub_mul_comm, Matrix.mul_smul]

end Matrix
