/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Data.Matrix.OccCount
public import TauCeti.Data.SignType.Lagrange
public import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.SemiringInverse
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Finite sign determination

`SignType.lagrangeCoeff` gives the coefficients of the Lagrange indicator
polynomials on `{-1,0,1}`. The full ternary moment matrix `fullMatrix` has one row
per exponent word and one column per sign word. Its tensor inverse `fullInverse`
is both a left and a right inverse; `fullInverse_mulVec` recovers occurrence
counts from all sign moments, including when the coordinate set is empty.

The full matrix is built from the one-coordinate matrix `coordMatrix`, with rows the
exponents `0, 1, 2`, columns the signs, and entries `σ ^ e` (so `0 ^ 0 = 1`). This matrix is
invertible over `ℚ`, with inverse `coordInverse` given by the Lagrange indicators. The full
matrix and its inverse are Kronecker products along any splitting of the coordinates
(`fullMatrix_sum`, `fullInverse_sum`), so for `n + 1` coordinates they are the Kronecker
products of the one-coordinate matrices with the full matrices for `n` coordinates
(`fullMatrix_fin_succ`, `fullInverse_fin_succ`).

Here `X` indexes observations and `J` indexes the sign queries.

## References

For the full ternary moment matrix and finite sign determination, see
S. Basu, R. Pollack, M.-F. Roy,
[*Algorithms in Real Algebraic Geometry*, 2nd ed.](https://doi.org/10.1007/3-540-33099-2),
Chapter 10, and C. Cohen, A. Mahboubi,
[Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination]
(https://doi.org/10.2168/LMCS-8(1:2)2012), LMCS 8(1), 2012.
-/

public section

open scoped Matrix Kronecker

open Function (occCount)

namespace TauCeti.SignDetermination

open SignType

variable {X : Type*} [Fintype X]
variable (J : Type*) [Fintype J] [DecidableEq J]

/-- The full ternary moment matrix has one row per exponent word and one
column per sign word. An empty coordinate set gives the one-by-one matrix. -/
def fullMatrix : Matrix (J → Fin 3) (J → SignType) ℚ :=
  Matrix.of fun e σ => ∏ j, (σ j : ℚ) ^ (e j).val

omit [DecidableEq J] in
/-- The full matrix is the moment matrix for all sign columns and ternary exponent rows. -/
theorem fullMatrix_def : fullMatrix J =
    Matrix.of (fun (e : J → Fin 3) (σ : J → SignType) => ∏ j, (σ j : ℚ) ^ (e j).val) := (rfl)

/-- Tensor product of the one-coordinate inverse coefficients. -/
def fullInverse : Matrix (J → SignType) (J → Fin 3) ℚ :=
  Matrix.of fun σ e => ∏ j, lagrangeCoeff (σ j) (e j)

omit [DecidableEq J] in
@[simp, grind =]
theorem fullMatrix_apply (e : J → Fin 3) (σ : J → SignType) :
    fullMatrix J e σ = ∏ j, (σ j : ℚ) ^ (e j).val := (rfl)

omit [DecidableEq J] in
@[simp, grind =]
theorem fullInverse_apply (σ : J → SignType) (e : J → Fin 3) :
    fullInverse J σ e = ∏ j, lagrangeCoeff (σ j) (e j) := (rfl)

/-- `fullInverse` is a left inverse of `fullMatrix` for every finite number of
sign queries, including zero. -/
@[simp, grind =]
theorem fullInverse_mul_fullMatrix : fullInverse J * fullMatrix J = 1 := by
  classical
  ext σ τ
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [fullInverse_apply, fullMatrix_apply]
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (j : J) (e : Fin 3) => lagrangeCoeff (σ j) e * (τ j : ℚ) ^ e.val)]
  simp only [sum_lagrangeCoeff_mul_pow]
  by_cases heq : σ = τ
  · subst τ
    simp
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp heq
    rw [ite_eq_right heq]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

/-- The tensor inverse is also a right inverse of the full ternary moment matrix. -/
@[simp, grind =]
theorem fullMatrix_mul_fullInverse : fullMatrix J * fullInverse J = 1 := by
  classical
  apply (Matrix.mul_eq_one_comm_of_card_eq (J → SignType) (J → Fin 3) ℚ
    (A := fullInverse J) (B := fullMatrix J) ?_).mp
    (fullInverse_mul_fullMatrix J)
  simp only [Fintype.card_fun]
  have hs : Fintype.card SignType = Fintype.card (Fin 3) := by decide
  rw [hs]

/-- The full sign matrix maps the actual multiplicities to the sign moments. -/
theorem fullMatrix_mulVec_occCount (obs : X → (J → SignType)) :
    fullMatrix J *ᵥ (fun σ => (occCount obs σ : ℚ)) =
      fun e => ∑ x, ∏ j, (obs x j : ℚ) ^ (e j).val := by
  simpa only [fullMatrix_def, id_eq] using
    Function.mulVec_occCount obs id Function.injective_id (fun x => ⟨obs x, rfl⟩)
      (fun (e : J → Fin 3) σ => ∏ j, (σ j : ℚ) ^ (e j).val)

/-- Explicit inversion of all ternary moments recovers each actual sign count. -/
theorem fullInverse_mulVec (obs : X → (J → SignType)) :
    fullInverse J *ᵥ (fun e => ∑ x, ∏ j, (obs x j : ℚ) ^ (e j).val) =
      fun σ => (occCount obs σ : ℚ) := by
  rw [← fullMatrix_mulVec_occCount, Matrix.mulVec_mulVec,
    fullInverse_mul_fullMatrix, Matrix.one_mulVec]

end TauCeti.SignDetermination

/-! ### The one-coordinate matrix and Kronecker products -/

namespace TauCeti.SignDetermination

open SignType

variable (J : Type*) [Fintype J]

/-- The one-coordinate sign moment matrix: its rows are the exponents `0, 1, 2`, its columns
are the signs, and its entry at `(e, σ)` is `σ ^ e`, with `0 ^ 0 = 1`. -/
def coordMatrix : Matrix (Fin 3) SignType ℚ :=
  Matrix.of fun e σ => (σ : ℚ) ^ e.val

/-- The inverse of the one-coordinate sign moment matrix, whose rows are the coefficients of
the Lagrange indicator polynomials on `{-1, 0, 1}`. -/
def coordInverse : Matrix SignType (Fin 3) ℚ :=
  Matrix.of lagrangeCoeff

@[simp, grind =]
theorem coordMatrix_apply (e : Fin 3) (σ : SignType) : coordMatrix e σ = (σ : ℚ) ^ e.val :=
  (rfl)

@[simp, grind =]
theorem coordInverse_apply (σ : SignType) (e : Fin 3) : coordInverse σ e = lagrangeCoeff σ e :=
  (rfl)

/-- `coordInverse` is a left inverse of the one-coordinate sign moment matrix. -/
@[simp, grind =]
theorem coordInverse_mul_coordMatrix : coordInverse * coordMatrix = 1 := by
  ext σ τ
  simp [Matrix.mul_apply, Matrix.one_apply]

/-- `coordInverse` is a right inverse of the one-coordinate sign moment matrix. -/
@[simp, grind =]
theorem coordMatrix_mul_coordInverse : coordMatrix * coordInverse = 1 :=
  (Matrix.mul_eq_one_comm_of_equiv SignType.fin3Equiv.toEquiv).mp coordInverse_mul_coordMatrix

/-- The one-coordinate sign moment matrix is invertible over `ℚ`, for any ordering of the
signs as its columns. -/
theorem isUnit_coordMatrix_submatrix (e : Fin 3 ≃ SignType) :
    IsUnit (coordMatrix.submatrix id e) := by
  refine ⟨⟨coordMatrix.submatrix id e, coordInverse.submatrix e id, ?_, ?_⟩, rfl⟩
  · rw [Matrix.submatrix_mul_equiv, coordMatrix_mul_coordInverse, Matrix.submatrix_id_id]
  · rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, coordInverse_mul_coordMatrix,
      Matrix.submatrix_one_equiv]

/-- The full ternary moment matrix is invertible over `ℚ`, for any ordering of the sign words
as its columns. -/
theorem isUnit_fullMatrix_submatrix [DecidableEq J] (e : (J → Fin 3) ≃ (J → SignType)) :
    IsUnit ((fullMatrix J).submatrix id e) := by
  refine ⟨⟨(fullMatrix J).submatrix id e, (fullInverse J).submatrix e id, ?_, ?_⟩, rfl⟩
  · rw [Matrix.submatrix_mul_equiv, fullMatrix_mul_fullInverse, Matrix.submatrix_id_id]
  · rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, fullInverse_mul_fullMatrix,
      Matrix.submatrix_one_equiv]

/-- With no coordinates, every entry of the full ternary moment matrix is the empty
product `1`. -/
theorem fullMatrix_of_isEmpty [IsEmpty J] : fullMatrix J = Matrix.of fun _ _ => 1 := by
  ext e σ
  simp

/-- With no coordinates, every entry of the tensor inverse is the empty product `1`. -/
theorem fullInverse_of_isEmpty [IsEmpty J] : fullInverse J = Matrix.of fun _ _ => 1 := by
  ext σ e
  simp

/-- With a single coordinate, the full ternary moment matrix is the one-coordinate matrix. -/
theorem fullMatrix_unique [Unique J] :
    fullMatrix J =
      coordMatrix.submatrix (Equiv.funUnique J (Fin 3)) (Equiv.funUnique J SignType) := by
  ext e σ
  simp

/-- With a single coordinate, the tensor inverse is the one-coordinate inverse. -/
theorem fullInverse_unique [Unique J] :
    fullInverse J =
      coordInverse.submatrix (Equiv.funUnique J SignType) (Equiv.funUnique J (Fin 3)) := by
  ext σ e
  simp

variable (K : Type*) [Fintype K]

/-- **Kronecker-product identity.** Splitting the coordinates as `J ⊕ K` splits the full
ternary moment matrix as the Kronecker product of the full matrices for `J` and `K`. -/
theorem fullMatrix_sum :
    fullMatrix (J ⊕ K) =
      (fullMatrix J ⊗ₖ fullMatrix K).submatrix (Equiv.sumArrowEquivProdArrow J K (Fin 3))
        (Equiv.sumArrowEquivProdArrow J K SignType) := by
  ext e σ
  simp [Fintype.prod_sum_type]

/-- Splitting the coordinates as `J ⊕ K` splits the tensor inverse as the Kronecker product of
the tensor inverses for `J` and `K`. -/
theorem fullInverse_sum :
    fullInverse (J ⊕ K) =
      (fullInverse J ⊗ₖ fullInverse K).submatrix (Equiv.sumArrowEquivProdArrow J K SignType)
        (Equiv.sumArrowEquivProdArrow J K (Fin 3)) := by
  ext σ e
  simp [Fintype.prod_sum_type]

/-- **Kronecker-product identity.** The full ternary moment matrix for `n + 1` coordinates is
the Kronecker product of the one-coordinate matrix, for coordinate `0`, with the full matrix
for the remaining `n` coordinates. -/
theorem fullMatrix_fin_succ (n : ℕ) :
    fullMatrix (Fin (n + 1)) =
      (coordMatrix ⊗ₖ fullMatrix (Fin n)).submatrix (Fin.consEquiv fun _ ↦ Fin 3).symm
        (Fin.consEquiv fun _ ↦ SignType).symm := by
  ext e σ
  simp [Fin.prod_univ_succ, Fin.tail]

/-- The tensor inverse for `n + 1` coordinates is the Kronecker product of the one-coordinate
inverse, for coordinate `0`, with the tensor inverse for the remaining `n` coordinates. -/
theorem fullInverse_fin_succ (n : ℕ) :
    fullInverse (Fin (n + 1)) =
      (coordInverse ⊗ₖ fullInverse (Fin n)).submatrix (Fin.consEquiv fun _ ↦ SignType).symm
        (Fin.consEquiv fun _ ↦ Fin 3).symm := by
  ext σ e
  simp [Fin.prod_univ_succ, Fin.tail]

end TauCeti.SignDetermination
