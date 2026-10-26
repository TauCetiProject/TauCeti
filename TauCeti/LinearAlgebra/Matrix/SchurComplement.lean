/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Reciprocal diagonal entries of an inverse as scalar Schur complements

For a square matrix `A` and an index `i`, write `B` for the principal submatrix of `A` on the
indices other than `i`. When `B` is invertible, the reciprocal of the diagonal entry `(A⁻¹) i i`
is the scalar Schur complement `A i i - aᵢ ⬝ᵥ B⁻¹ *ᵥ aⁱ` of `B` in `A`, where `aᵢ` and `aⁱ` are
the `i`-th row and column of `A` with the entry `A i i` removed. This holds also when `A` is
singular, both sides then being zero, and when `i` is the only index, `B` then being empty.

## Main results

* `Matrix.inv_inv_apply_self_eq_sub`: the reciprocal of `(A⁻¹) i i` is the scalar Schur
  complement of the complementary principal block, whenever that block is invertible.
* `Matrix.PosDef.inv_inv_apply_self_eq_sub`: the same identity for positive-definite matrices,
  whose principal blocks are always invertible.
-/

public section

namespace Matrix

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
