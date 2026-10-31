/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Schur complements

Generalized Schur complements of positive-semidefinite block matrices are positive
semidefinite. The inverse used in the complement need only be Hermitian and satisfy
`P * D * P = P`; in particular the result applies to a singular block's pseudoinverse.

For a square matrix `A` and an index `i`, write `B` for the principal submatrix of `A` on the
indices other than `i`. When `B` is invertible, the reciprocal of the diagonal entry `(A⁻¹) i i`
is the scalar Schur complement `A i i - aᵢ ⬝ᵥ B⁻¹ *ᵥ aⁱ` of `B` in `A`, where `aᵢ` and `aⁱ` are
the `i`-th row and column of `A` with the entry `A i i` removed. This holds also when `A` is
singular, both sides then being zero, and when `i` is the only index, `B` then being empty.

## Main results

* `Matrix.PosSemidef.schur_complement₂₂` and `Matrix.PosSemidef.schur_complement₁₁`:
  positivity of generalized Schur complements, without invertibility of the pivot block.
* `Matrix.inv_inv_apply_self_eq_sub`: the reciprocal of `(A⁻¹) i i` is the scalar Schur
  complement of the complementary principal block, whenever that block is invertible.
* `Matrix.PosDef.inv_inv_apply_self_eq_sub`: the same identity for positive-definite matrices,
  whose principal blocks are always invertible.
-/

public section

namespace Matrix

section Generalized

variable {m n R : Type*} [Ring R] [PartialOrder R] [StarRing R]

/-- A generalized Schur complement of the bottom-right block of a positive-semidefinite
matrix is positive semidefinite. Only the Hermitian property and the second generalized-inverse
equation are needed, so the block may be singular. -/
theorem PosSemidef.schur_complement₂₂ [Finite m] [Fintype n]
    {A : Matrix m m R} {B : Matrix m n R}
    {D P : Matrix n n R} (h : (fromBlocks A B Bᴴ D).PosSemidef)
    (hP : P.IsHermitian) (hPDP : P * D * P = P) :
    (A - B * P * Bᴴ).PosSemidef := by
  classical
  let := Fintype.ofFinite m
  have hcancel : B * P * D * P = B * P := by
    simpa only [Matrix.mul_assoc] using congrArg (B * ·) hPDP
  have hcompress :
      fromCols 1 (-(B * P)) * fromBlocks A B Bᴴ D * (fromCols 1 (-(B * P)))ᴴ =
        A - B * P * Bᴴ := by
    simp only [conjTranspose_fromCols_eq_fromRows_conjTranspose, conjTranspose_one,
      conjTranspose_neg, conjTranspose_mul, hP.eq,
      fromCols_mul_fromBlocks, fromCols_mul_fromRows, Matrix.one_mul, Matrix.mul_one,
      Matrix.add_mul, Matrix.neg_mul, Matrix.mul_neg,
      ← Matrix.mul_assoc, hcancel]
    abel
  rw [← hcompress]
  exact h.mul_mul_conjTranspose_same _

/-- A generalized Schur complement of the top-left block of a positive-semidefinite matrix
is positive semidefinite, including when that block is singular. -/
theorem PosSemidef.schur_complement₁₁ [Fintype m] [Finite n]
    {A P : Matrix m m R} {B : Matrix m n R} {D : Matrix n n R}
    (h : (fromBlocks A B Bᴴ D).PosSemidef)
    (hP : P.IsHermitian) (hPAP : P * A * P = P) :
    (D - Bᴴ * P * B).PosSemidef := by
  have hswap := h.submatrix (Equiv.sumComm n m)
  rw [Equiv.sumComm_apply, fromBlocks_submatrix_sum_swap_sum_swap] at hswap
  have hswap' : (fromBlocks D Bᴴ (Bᴴ)ᴴ A).PosSemidef := by
    simpa only [conjTranspose_conjTranspose] using hswap
  simpa only [conjTranspose_conjTranspose] using hswap'.schur_complement₂₂ hP hPAP

end Generalized

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

/-- The reciprocal of a diagonal entry `(A⁻¹) i i` of the inverse of a square matrix is the scalar
Schur complement of the principal block of `A` away from `i`, provided that block is invertible.
Both sides vanish when `A` is singular. -/
theorem inv_inv_apply_self_eq_sub (A : Matrix n n K) (i : n)
    (hB : IsUnit (A.submatrix (↑) (↑) : Matrix {a // a ≠ i} {a // a ≠ i} K).det) :
    (A⁻¹ i i)⁻¹ =
      A i i - (fun a : {a // a ≠ i} ↦ A i a) ⬝ᵥ
        ((A.submatrix (↑) (↑) : Matrix {a // a ≠ i} {a // a ≠ i} K)⁻¹ *ᵥ fun b ↦ A b i) := by
  set B : Matrix {a // a ≠ i} {a // a ≠ i} K := A.submatrix (↑) (↑)
  set s := A i i - (fun a : {a // a ≠ i} ↦ A i a) ⬝ᵥ (B⁻¹ *ᵥ fun b ↦ A b i)
  let : Invertible B := invertibleOfIsUnitDet B hB
  let e := Equiv.sumCompl (· = i)
  have hdet : A.det = B.det * s := by
    have hblk : A.submatrix e e = fromBlocks (A.submatrix (↑) (↑)) (A.submatrix (↑) (↑))
        (A.submatrix (↑) (↑)) B := by
      ext (x | x) (y | y) <;> rfl
    rw [← det_submatrix_equiv_self e A, hblk, det_fromBlocks₂₂,
      det_unique (_ : Matrix {a // a = i} {a // a = i} K),
      show (default : {a // a = i}) = ⟨i, rfl⟩ from Subsingleton.elim _ _]
    congr 1
    simp only [s, sub_apply, submatrix_apply, invOf_eq_nonsing_inv, Matrix.mul_apply, dotProduct,
      mulVec, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  have hadj : adjugate A i i = B.det := by
    have hblk : (A.updateRow i (Pi.single i 1)).submatrix e e =
        fromBlocks 1 0 (A.submatrix (↑) (↑)) B := by
      ext (⟨x, rfl⟩ | ⟨x, hx⟩) (⟨y, hy⟩ | ⟨y, hy⟩)
      · simp [e, updateRow_apply, hy.symm]
      · simp [e, updateRow_apply, hy]
      · simp [e, updateRow_apply, hx, B]
      · simp [e, updateRow_apply, hx, B]
    rw [adjugate_apply, ← det_submatrix_equiv_self e, hblk, det_fromBlocks_zero₁₂, det_one,
      one_mul]
  have hB0 : B.det ≠ 0 := hB.ne_zero
  rw [inv_def, smul_apply, hadj, hdet, Ring.inverse_eq_inv', smul_eq_mul, mul_comm,
    ← div_eq_mul_inv, inv_div, mul_div_cancel_left₀ s hB0]

/-- The reciprocal of a diagonal entry `(A⁻¹) i i` of the inverse of a positive-definite real
matrix is the scalar Schur complement of the principal block of `A` away from `i`. -/
theorem PosDef.inv_inv_apply_self_eq_sub {A : Matrix n n ℝ} (hA : A.PosDef) (i : n) :
    (A⁻¹ i i)⁻¹ =
      A i i - (fun a : {a // a ≠ i} ↦ A i a) ⬝ᵥ
        ((A.submatrix (↑) (↑) : Matrix {a // a ≠ i} {a // a ≠ i} ℝ)⁻¹ *ᵥ fun b ↦ A b i) :=
  A.inv_inv_apply_self_eq_sub i
    (isUnit_iff_ne_zero.2 (hA.submatrix Subtype.val_injective).det_pos.ne')

end Matrix
