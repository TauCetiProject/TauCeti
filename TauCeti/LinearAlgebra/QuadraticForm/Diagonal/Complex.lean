/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Analysis.Complex.Sqrt
public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Normalization

/-!
# The complex sum-of-squares normalization

Over `ℂ` every nonzero scalar has a principal square root `z ^ (2⁻¹ : ℂ)`. Dividing each member
of an orthogonal basis `b` of a complex quadratic form `Q` by the principal square root of its
value `Q (b i) ≠ 0` gives a basis with identity Gram matrix, and coordinates in that basis are a
specified isometry from `Q` to the standard sum of squares. This is the specialization to principal
square roots of `QuadraticForm.isometryEquivSumSquaresOfMulSelf`; the orthogonal basis is retained
as data, and the isometry sends `b i` to `Q (b i) ^ (2⁻¹ : ℂ) • Pi.single i 1`.

For the diagonal form `x₁² + 2 x₂²` on `ℂ²` with its standard basis, the normalized basis is
`e₁, e₂ / √2`: its Gram matrix is the identity, whereas `e₂` itself has value `2`, so the standard
basis has Gram matrix `diag(1, 2)`.

## Main definitions

* `QuadraticForm.complexNormalizedBasis`: the members `(Q (b i) ^ (2⁻¹ : ℂ))⁻¹ • b i` of the
  normalized basis.
* `QuadraticForm.complexIsometryEquivSumSquares`: the specified isometry to the sum of squares.

## Main results

* `QuadraticForm.toMatrix_complexNormalizedBasis`: the normalized basis has identity Gram matrix.
* `QuadraticForm.complexIsometryEquivSumSquares_apply_basis`: the isometry sends `b i` to
  `Q (b i) ^ (2⁻¹ : ℂ) • Pi.single i 1`.
* `QuadraticForm.complexNormalizedBasis_weightedSumSquares_one_two`: for `diag(1, 2)` the normalized
  basis is `e₁, e₂ / √2`, and `QuadraticForm.toMatrix_basisFun_weightedSumSquares_one_two` records
  that the unnormalized standard basis has Gram matrix `diag(1, 2)`.
-/

public section

open Module QuadraticMap

namespace QuadraticForm

variable {M ι : Type*} [AddCommGroup M] [Module ℂ M]

/-- The complex normalization of a basis `b` on which `Q` takes nonzero values: each `b i` is
divided by the principal square root of `Q (b i)`. -/
noncomputable def complexNormalizedBasis (Q : QuadraticForm ℂ M) (b : Basis ι ℂ M)
    (h0 : ∀ i, Q (b i) ≠ 0) : Basis ι ℂ M :=
  b.unitsSMul fun i => (Complex.sqrtUnit (h0 i))⁻¹

@[simp]
theorem complexNormalizedBasis_apply (Q : QuadraticForm ℂ M) (b : Basis ι ℂ M)
    (h0 : ∀ i, Q (b i) ≠ 0) (i : ι) :
    Q.complexNormalizedBasis b h0 i = (Q (b i) ^ (2⁻¹ : ℂ))⁻¹ • b i := by
  rw [complexNormalizedBasis, Basis.unitsSMul_apply, Units.smul_def, Units.val_inv_eq_inv_val,
    Complex.val_sqrtUnit, Complex.sqrt]

/-- Each member of the complex normalized basis has value `1`. -/
theorem apply_complexNormalizedBasis_eq_one (Q : QuadraticForm ℂ M) (b : Basis ι ℂ M)
    (h0 : ∀ i, Q (b i) ≠ 0) (i : ι) : Q (Q.complexNormalizedBasis b h0 i) = 1 :=
  apply_unitsSMul_inv_eq_one (fun i => Complex.sqrtUnit_mul_self (h0 i)) i

/-- The complex normalization of an orthogonal basis is orthogonal. -/
theorem isOrthoᵢ_complexNormalizedBasis {Q : QuadraticForm ℂ M} {b : Basis ι ℂ M}
    (hb : (associated Q).IsOrthoᵢ b) (h0 : ∀ i, Q (b i) ≠ 0) :
    (associated Q).IsOrthoᵢ (Q.complexNormalizedBasis b h0) :=
  hb.unitsSMul _

variable [Fintype ι]

/-- The complex normalization of an orthogonal basis has identity Gram matrix. -/
theorem toMatrix_complexNormalizedBasis [DecidableEq ι] {Q : QuadraticForm ℂ M}
    {b : Basis ι ℂ M} (hb : (associated Q).IsOrthoᵢ b) (h0 : ∀ i, Q (b i) ≠ 0) :
    Q.toMatrix (Q.complexNormalizedBasis b h0) = 1 :=
  toMatrix_unitsSMul_inv hb fun i => Complex.sqrtUnit_mul_self (h0 i)

/-- The specified complex sum-of-squares normalization of an orthogonal basis `b` on which `Q`
takes nonzero values: coordinates in `Q.complexNormalizedBasis b h0`, as an isometry from `Q` to
the standard sum of squares. -/
noncomputable def complexIsometryEquivSumSquares (Q : QuadraticForm ℂ M) (b : Basis ι ℂ M)
    (hb : (associated Q).IsOrthoᵢ b) (h0 : ∀ i, Q (b i) ≠ 0) :
    Q.IsometryEquiv (weightedSumSquares ℂ (1 : ι → ℂ)) :=
  Q.isometryEquivSumSquaresOfMulSelf b hb (fun i => Complex.sqrtUnit (h0 i))
    fun i => Complex.sqrtUnit_mul_self (h0 i)

variable {Q : QuadraticForm ℂ M} {b : Basis ι ℂ M} (hb : (associated Q).IsOrthoᵢ b)
  (h0 : ∀ i, Q (b i) ≠ 0)

/-- The specified complex normalization is the coordinate isometry of the complex normalized
basis. -/
theorem complexIsometryEquivSumSquares_def :
    Q.complexIsometryEquivSumSquares b hb h0 =
      Q.isometryEquivSumSquaresOfIsOrthoᵢ (Q.complexNormalizedBasis b h0)
        (isOrthoᵢ_complexNormalizedBasis hb h0) (apply_complexNormalizedBasis_eq_one Q b h0) := by
  simp only [complexIsometryEquivSumSquares, isometryEquivSumSquaresOfMulSelf_def,
    complexNormalizedBasis]

@[simp]
theorem complexIsometryEquivSumSquares_apply (x : M) :
    Q.complexIsometryEquivSumSquares b hb h0 x = (Q.complexNormalizedBasis b h0).equivFun x := by
  rw [complexIsometryEquivSumSquares_def, isometryEquivSumSquaresOfIsOrthoᵢ_apply]

@[simp]
theorem complexIsometryEquivSumSquares_symm_apply (w : ι → ℂ) :
    (Q.complexIsometryEquivSumSquares b hb h0).symm w =
      ∑ i, w i • Q.complexNormalizedBasis b h0 i := by
  rw [complexIsometryEquivSumSquares_def, isometryEquivSumSquaresOfIsOrthoᵢ_symm_apply]

variable [DecidableEq ι]

/-- The specified complex normalization sends `b i` to the principal square root of `Q (b i)`
times the `i`-th standard coordinate vector. -/
theorem complexIsometryEquivSumSquares_apply_basis (i : ι) :
    Q.complexIsometryEquivSumSquares b hb h0 (b i) = Q (b i) ^ (2⁻¹ : ℂ) • Pi.single i 1 := by
  rw [complexIsometryEquivSumSquares, isometryEquivSumSquaresOfMulSelf_apply_basis,
    Complex.val_sqrtUnit, Complex.sqrt]

/-- The inverse of the specified complex normalization sends the `i`-th standard coordinate vector
to the `i`-th member of the complex normalized basis. -/
theorem complexIsometryEquivSumSquares_symm_single (i : ι) :
    (Q.complexIsometryEquivSumSquares b hb h0).symm (Pi.single i 1) =
      Q.complexNormalizedBasis b h0 i := by
  rw [complexIsometryEquivSumSquares_def, isometryEquivSumSquaresOfIsOrthoᵢ_symm_single]

/-! ### The form `diag(1, 2)` -/

/-- The diagonal form `x₁² + 2 x₂²` takes nonzero values on the standard basis of `ℂ²`. -/
theorem weightedSumSquares_one_two_basisFun_ne_zero (i : Fin 2) :
    weightedSumSquares ℂ ![(1 : ℂ), 2] (Pi.basisFun ℂ (Fin 2) i) ≠ 0 := by
  rw [Pi.basisFun_apply, weightedSumSquares_apply_single]
  fin_cases i <;> simp

/-- In the standard basis of `ℂ²` the diagonal form `x₁² + 2 x₂²` has Gram matrix `diag(1, 2)`,
which is not the identity: retaining `e₂` leaves its value `2`. -/
theorem toMatrix_basisFun_weightedSumSquares_one_two :
    QuadraticForm.toMatrix (Pi.basisFun ℂ (Fin 2)) (weightedSumSquares ℂ ![(1 : ℂ), 2]) =
      Matrix.diagonal ![1, 2] := by
  rw [toMatrix_eq_toMatrix', toMatrix'_weightedSumSquares]
  simp only [smul_eq_mul, mul_one]

/-- For the diagonal form `x₁² + 2 x₂²` on `ℂ²`, the complex normalization of the standard basis
is `e₁, e₂ / √2`. -/
theorem complexNormalizedBasis_weightedSumSquares_one_two :
    ⇑(complexNormalizedBasis (weightedSumSquares ℂ ![(1 : ℂ), 2]) (Pi.basisFun ℂ (Fin 2))
        weightedSumSquares_one_two_basisFun_ne_zero) =
      ![Pi.single 0 1, ((√2 : ℝ) : ℂ)⁻¹ • Pi.single 1 1] := by
  have h2 : (2 : ℂ) ^ (2⁻¹ : ℂ) = ((√2 : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by norm_num)]
    norm_num
  ext i : 1
  rw [complexNormalizedBasis_apply, Pi.basisFun_apply, weightedSumSquares_apply_single]
  fin_cases i
  · simp
  · simp [h2]

end QuadraticForm
