/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.GeometricMean

/-!
# The positive semidefinite solution of `A * S * A = T`

The Loewner order on square matrices makes `Matrix n n 𝕜` an algebra with a continuous functional
calculus, so `TauCeti.geometricMean` applies to it: for `S` positive definite and `T` positive
semidefinite there is exactly one positive semidefinite `A` with `A * S * A = T`, namely
`TauCeti.geometricMean S⁻¹ʳ T`, which is the classical matrix
`√(S⁻¹) * √(√S * T * √S) * √(S⁻¹)`.

Read through covariance matrices, that matrix is the linear map pushing a centred Gaussian law of
covariance `S` forward to one of covariance `T`, that is, the Brenier map between two Gaussians.

The solution is Hermitian, so for positive definite `S` and positive semidefinite `T` it solves
the congruence equation `A * S * Aᴴ = T` as well; when `T` is positive definite the solution is
positive definite itself, and its inverse is the solution `TauCeti.geometricMean T⁻¹ʳ S` of the
reversed equation.

## Main results

* `Matrix.PosDef.existsUnique_posSemidef_mul_mul`: existence and uniqueness of that matrix.
* `Matrix.PosDef.geometricMean_ringInverse_eq_sqrt_mul_mul_sqrt`: that matrix is the congruence
  `(√S)⁻¹ * √(√S * T * √S) * (√S)⁻¹` of the positive square root of `√S * T * √S`.
* `Matrix.isHermitian_geometricMean` and `Matrix.PosDef.posDef_geometricMean_ringInverse`: the
  geometric mean is Hermitian, and this one is positive definite when `T` is.
* `Matrix.PosDef.mul_mul_conjTranspose_geometricMean`: the solution satisfies `A * S * Aᴴ = T`.
* `Matrix.PosDef.inv_geometricMean_ringInverse`: reversing `S` and `T` inverts the solution.
-/

public section

noncomputable section

open Ring TauCeti
open scoped ComplexOrder MatrixOrder

namespace Matrix

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] {S T : Matrix n n 𝕜}

/-- For a positive definite `S` and a positive semidefinite `T` there is exactly one positive
semidefinite matrix `A` with `A * S * A = T`; it is `TauCeti.geometricMean S⁻¹ʳ T`. -/
theorem PosDef.existsUnique_posSemidef_mul_mul (hS : S.PosDef) (hT : T.PosSemidef) :
    ∃! A : Matrix n n 𝕜, A.PosSemidef ∧ A * S * A = T := by
  classical
  refine ⟨geometricMean S⁻¹ʳ T,
    ⟨nonneg_iff_posSemidef.mp (geometricMean_nonneg _ _), ?_⟩, ?_⟩
  · exact geometricMean_ringInverse_mul_mul_geometricMean_ringInverse hS.isStrictlyPositive
      hT.nonneg
  · rintro A ⟨hA, hAST⟩
    exact eq_geometricMean_ringInverse_of_mul_mul hAST hS.isStrictlyPositive hA.nonneg

/-! ### The standard positive matrix, its Hermitian symmetry, and its inverse -/

section Symmetry

variable [DecidableEq n]

/-- **The standard positive matrix.** For a positive-definite `S` the matrix
`geometricMean S⁻¹ʳ T` is the congruence `(√S)⁻¹ * √(√S * T * √S) * (√S)⁻¹` of the positive
square root of `√S * T * √S` by the inverse `(√S)⁻¹` of the positive square root of `S`; when `T`
is positive semidefinite it is the solution `A` of `A * S * A = T`. -/
theorem PosDef.geometricMean_ringInverse_eq_sqrt_mul_mul_sqrt (hS : S.PosDef) :
    geometricMean S⁻¹ʳ T =
      (CFC.sqrt S)⁻¹ * CFC.sqrt (CFC.sqrt S * T * CFC.sqrt S) * (CFC.sqrt S)⁻¹ := by
  have hSdet : IsUnit (CFC.sqrt S).det :=
    Matrix.isUnit_iff_isUnit_det (CFC.sqrt S) |>.mp (hS.isStrictlyPositive.isUnit_cfcSqrt S)
  rw [← Matrix.nonsing_inv_eq_ringInverse, geometricMean_eq_sqrt_mul_mul,
    ← Matrix.nonsing_inv_eq_ringInverse, ← hS.posSemidef.inv_sqrt,
    Matrix.nonsing_inv_nonsing_inv (A := CFC.sqrt S) hSdet]

/-- **The solution is Hermitian.** The geometric mean
`√a * √(√a⁻¹ * b * √a⁻¹) * √a` is a Hermitian matrix sandwiched between two copies of a
Hermitian matrix: each square root is nonnegative, hence Hermitian. No positivity hypothesis is
needed, so this is a statement about `geometricMean a b` for every `a` and `b`; in particular the
solution `A` of `A * S * A = T` is Hermitian whenever `S` is positive definite and `T` is
positive semidefinite. -/
theorem isHermitian_geometricMean {a b : Matrix n n 𝕜} : (geometricMean a b).IsHermitian := by
  rw [geometricMean_eq_sqrt_mul_mul]
  have hX : (CFC.sqrt a).IsHermitian :=
    (nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg _)).isHermitian
  have hY : (CFC.sqrt (Ring.inverse (CFC.sqrt a) * b * Ring.inverse (CFC.sqrt a))).IsHermitian :=
    (nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg _)).isHermitian
  simpa only [hX.eq] using isHermitian_conjTranspose_mul_mul (CFC.sqrt a) hY

/-- The standard positive matrix of two positive-definite matrices is positive definite: the
geometric mean of a strictly positive and of a strictly positive element is strictly positive. -/
theorem PosDef.posDef_geometricMean_ringInverse (hS : S.PosDef) (hT : T.PosDef) :
    (geometricMean S⁻¹ʳ T).PosDef := by
  refine Matrix.isStrictlyPositive_iff_posDef.mp ?_
  exact isStrictlyPositive_geometricMean (a := Ring.inverse S) (b := T)
    hS.isStrictlyPositive.ringInverse hT.isStrictlyPositive

/-- **The congruence form.** The solution `A` of `A * S * A = T` for positive-definite `S` and
positive-semidefinite `T` is Hermitian by `isHermitian_geometricMean`, so it solves the
congruence `A * S * Aᴴ = T` as well. This is the form in which a covariance matrix transforms
under a change of variables; over the reals `Aᴴ` is the transpose `Aᵀ`. -/
@[simp]
theorem PosDef.mul_mul_conjTranspose_geometricMean (hS : S.PosDef) (hT : T.PosSemidef) :
    geometricMean S⁻¹ʳ T * S * (geometricMean S⁻¹ʳ T)ᴴ = T := by
  rw [isHermitian_geometricMean.eq,
    geometricMean_ringInverse_mul_mul_geometricMean_ringInverse hS.isStrictlyPositive hT.nonneg]

/-- **Reversing the equation inverts the solution.** The solution of `A * S * A = T`, inverted, is
the solution of `B * T * B = S`: the geometric mean commutes with inversion and is symmetric in
its two arguments. -/
@[simp]
theorem PosDef.inv_geometricMean_ringInverse (hS : S.PosDef) (hT : T.PosDef) :
    (geometricMean S⁻¹ʳ T)⁻¹ = geometricMean T⁻¹ʳ S := by
  have hS' : IsStrictlyPositive S⁻¹ʳ := hS.isStrictlyPositive.ringInverse
  have hT' : IsStrictlyPositive T⁻¹ʳ := hT.isStrictlyPositive.ringInverse
  calc (geometricMean S⁻¹ʳ T)⁻¹ = (geometricMean S⁻¹ʳ T)⁻¹ʳ :=
        Matrix.nonsing_inv_eq_ringInverse _
    _ = geometricMean S T⁻¹ʳ := by
        rw [← geometricMean_ringInverse_ringInverse hS' hT.isStrictlyPositive,
          inverse_inverse hS.isUnit]
    _ = geometricMean T⁻¹ʳ S := geometricMean_comm hS.isStrictlyPositive hT'

end Symmetry

end Matrix
