/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Determinants of matrices of multivariate polynomials

Let `A` be a square matrix with entries in `MvPolynomial σ R` whose `l`-th column has partial
degree at most `e l` in the variable `Xᵢ`. Every term of the Leibniz expansion of `det A` is, up
to sign, a product containing exactly one entry from each column, so `det A` has partial degree
at most `∑ l, e l` in `Xᵢ`.

The minors of a matrix `Z`, and of its powers, are polynomials in the entries of `Z`: they are
the values at `Z` of the corresponding minors of the generic matrix `Matrix.mvPolynomialX`.

The generic determinant is a non-zero-divisor over every commutative ring.
Translating the generic matrix by the identity and embedding into power series
reduces this to its constant coefficient being one.

## Main results

* `Matrix.degreeOf_det_le_sum`: the partial degree of a determinant is bounded by
  the sum of the column-wise partial-degree bounds.
* `Matrix.aeval_det_submatrix_mvPolynomialX` and `Matrix.aeval_det_submatrix_pow_mvPolynomialX`:
  the minors of a matrix `Z`, and of `Z ^ j`, are evaluations of minors of the generic matrix.
* `Matrix.det_mvPolynomialX_mem_nonZeroDivisors`: the generic determinant is regular.
-/

public section

namespace Matrix

open MvPolynomial Finset

section Degree

variable {R σ n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- If the `l`-th column of a matrix `A` of multivariate polynomials has partial degree at most
`e l` in `Xᵢ`, then `det A` has partial degree at most `∑ l, e l` in `Xᵢ`. -/
theorem degreeOf_det_le_sum (A : Matrix n n (MvPolynomial σ R)) (i : σ) (e : n → ℕ)
    (hA : ∀ k l, (A k l).degreeOf i ≤ e l) :
    A.det.degreeOf i ≤ ∑ l, e l := by
  rw [det_apply]
  refine (degreeOf_sum_le i univ _).trans (Finset.sup_le fun p _ ↦ ?_)
  calc
    (Equiv.Perm.sign p • ∏ l, A (p l) l).degreeOf i =
        (∏ l, A (p l) l).degreeOf i := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign p) with hp | hp
      · rw [hp, one_smul]
      · rw [hp, Units.neg_smul, one_smul, degreeOf_neg]
    _ ≤ ∑ l, (A (p l) l).degreeOf i := degreeOf_prod_le i univ _
    _ ≤ ∑ l, e l := Finset.sum_le_sum fun l _ ↦ hA (p l) l

/-- The generic determinant is a non-zero-divisor over every commutative ring,
including the zero ring and matrices of size zero. -/
theorem det_mvPolynomialX_mem_nonZeroDivisors :
    (mvPolynomialX n n R).det ∈ nonZeroDivisors (MvPolynomial (n × n) R) := by
  let t : MvPolynomial (n × n) R →ₐ[R] MvPolynomial (n × n) R :=
    aeval fun ij => X ij + C ((1 : Matrix n n R) ij.1 ij.2)
  let u : MvPolynomial (n × n) R →ₐ[R] MvPolynomial (n × n) R :=
    aeval fun ij => X ij - C ((1 : Matrix n n R) ij.1 ij.2)
  have hut : u.comp t = AlgHom.id R _ := by
    ext ij
    simp [t, u]
  have hleft : Function.LeftInverse u t := fun p => DFunLike.congr_fun hut p
  have ht : Function.Injective t := hleft.injective
  let f : MvPolynomial (n × n) R →+* MvPowerSeries (n × n) R :=
    MvPolynomial.coeToMvPowerSeries.ringHom.comp t.toRingHom
  have hf : Function.Injective f := (MvPolynomial.coe_injective _ _).comp ht
  apply mem_nonZeroDivisors_of_injective hf
  apply MvPowerSeries.mem_nonZeroDivisors_of_constantCoeff
  have hm : (MvPowerSeries.constantCoeff.comp f).mapMatrix (mvPolynomialX n n R) = 1 := by
    ext i j
    simp [f, t]
  -- Bundle the constant-coefficient evaluation so map_det applies to the ring homomorphism.
  change (MvPowerSeries.constantCoeff.comp f) (mvPolynomialX n n R).det ∈ _
  rw [RingHom.map_det, hm, det_one]
  exact one_mem _

end Degree

section Minors

variable {R S m n l : Type*} [CommRing R] [CommRing S] [Algebra R S] [Fintype l] [DecidableEq l]

/-- The minors of a matrix `Z` are the values at the entries of `Z` of the corresponding minors
of the generic matrix `Matrix.mvPolynomialX`. -/
theorem aeval_det_submatrix_mvPolynomialX (Z : Matrix m n S) (r : l → m) (c : l → n) :
    aeval (Function.uncurry Z) ((mvPolynomialX m n R).submatrix r c).det =
      (Z.submatrix r c).det := by
  rw [AlgHom.map_det, AlgHom.mapMatrix_apply, ← submatrix_map]
  congr 2
  ext i j
  rw [map_apply, mvPolynomialX_apply, aeval_X]
  exact Function.uncurry_apply_pair (f := Z) i j

/-- The minors of the `j`-th power of a matrix `Z` are the values at the entries of `Z` of the
corresponding minors of the `j`-th power of the generic matrix `Matrix.mvPolynomialX`. -/
theorem aeval_det_submatrix_pow_mvPolynomialX [Fintype n] [DecidableEq n] (Z : Matrix n n S)
    (j : ℕ) (r c : l → n) :
    aeval (Function.uncurry Z) ((mvPolynomialX n n R ^ j).submatrix r c).det =
      ((Z ^ j).submatrix r c).det := by
  rw [AlgHom.map_det, AlgHom.mapMatrix_apply, ← submatrix_map, ← AlgHom.mapMatrix_apply,
    map_pow]
  exact congrArg (fun A : Matrix n n S ↦ ((A ^ j).submatrix r c).det)
    (mvPolynomialX_mapMatrix_aeval R Z)

end Minors

end Matrix
