/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Completing a block of rows or columns to an invertible matrix

Let `e : m ⊕ p ≃ n` split a finite index type. A `p × n` matrix `x` whose square block on the
columns `e (p)` is invertible is the block of the rows `e (p)` of an invertible `n × n` matrix:
complete it by the rows of the identity on `e (m)`. The completed matrix is block lower triangular
along `e`, with diagonal blocks `1` and the square block of `x`, so its determinant is that of the
square block. In the same way an `n × m` matrix whose square block on the rows `e (m)` is
invertible is the block of the columns `e (m)` of an invertible matrix, completed by the columns of
the identity on `e (p)`.

Conversely, multiplying `k ∈ GL_n(R)` on the right by a `g` whose rows `e (p)` are those of the
identity does not change the rows `e (p)` of `k⁻¹`, and multiplies the columns `e (m)` of `k` by
the square block of `g` on `e (m)`, whose determinant is that of `g`. Two invertible matrices `k`,
`k'` whose inverses have the same rows `e (p)` differ by such a `g = k⁻¹ k'`, so the columns `e (m)`
of `k'` are those of `k` times an invertible `m × m` matrix.

## Main results

* `Matrix.GeneralLinearGroup.exists_submatrix_comp_inr_id_eq_of_isUnit_det`: a block of rows
  with an invertible square block is the block of rows of an invertible matrix.
* `Matrix.GeneralLinearGroup.exists_submatrix_id_comp_inl_eq_of_isUnit_det`: a block of columns
  with an invertible square block is the block of columns of an invertible matrix.
* `Matrix.GeneralLinearGroup.submatrix_inv_mul_of_rows_eq_one`,
  `Matrix.GeneralLinearGroup.submatrix_mul_of_rows_eq_one`,
  `Matrix.GeneralLinearGroup.det_eq_det_submatrix_of_rows_eq_one`: right multiplication by a
  matrix whose rows `e (p)` are those of the identity.
* `Matrix.GeneralLinearGroup.exists_submatrix_eq_mul_of_submatrix_inv_eq`: invertible matrices
  whose inverses have the same rows `e (p)` have the same columns `e (m)` up to `GL_m(R)` acting on
  the right.
-/

public section

namespace Matrix.GeneralLinearGroup

variable {R m p n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- **Completion of a block of rows.** For a splitting `e : m ⊕ p ≃ n`, a `p × n` matrix `x` whose
square block on the columns `e (p)` is invertible is the block of the rows `e (p)` of an
invertible matrix, the one with the rows of the identity on `e (m)` and those of `x` on `e (p)`. -/
theorem exists_submatrix_comp_inr_id_eq_of_isUnit_det [Fintype p] [DecidableEq p] (e : m ⊕ p ≃ n)
    {x : Matrix p n R} (hx : IsUnit (x.submatrix id (e ∘ Sum.inr)).det) :
    ∃ k : GL n R, (k : Matrix n n R).submatrix (e ∘ Sum.inr) id = x := by
  classical
  have : Fintype m := Fintype.ofInjective (e ∘ Sum.inl) (e.injective.comp Sum.inl_injective)
  set N : Matrix n n R :=
    (fromRows ((1 : Matrix n n R).submatrix (e ∘ Sum.inl) id) x).submatrix e.symm id
  have hN : N.submatrix e e =
      fromBlocks 1 0 (x.submatrix id (e ∘ Sum.inl)) (x.submatrix id (e ∘ Sum.inr)) := by
    ext (i | i) (j | j) <;> simp [N, Matrix.one_apply, e.injective.eq_iff]
  have hNdet : IsUnit N.det := by
    rwa [← det_submatrix_equiv_self e, hN, det_fromBlocks_zero₁₂, det_one, one_mul]
  refine ⟨GeneralLinearGroup.mk'' N hNdet, ?_⟩
  ext i j
  simp [N]

/-- **Completion of a block of columns.** For a splitting `e : m ⊕ p ≃ n`, an `n × m` matrix `y`
whose square block on the rows `e (m)` is invertible is the block of the columns `e (m)` of an
invertible matrix, the one with the columns of `y` on `e (m)` and those of the identity on
`e (p)`. -/
theorem exists_submatrix_id_comp_inl_eq_of_isUnit_det [Fintype m] [DecidableEq m] (e : m ⊕ p ≃ n)
    {y : Matrix n m R} (hy : IsUnit (y.submatrix (e ∘ Sum.inl) id).det) :
    ∃ k : GL n R, (k : Matrix n n R).submatrix id (e ∘ Sum.inl) = y := by
  classical
  have : Fintype p := Fintype.ofInjective (e ∘ Sum.inr) (e.injective.comp Sum.inr_injective)
  set K : Matrix n n R :=
    (fromCols y ((1 : Matrix n n R).submatrix id (e ∘ Sum.inr))).submatrix id e.symm
  have hK : K.submatrix e e =
      fromBlocks (y.submatrix (e ∘ Sum.inl) id) 0 (y.submatrix (e ∘ Sum.inr) id) 1 := by
    ext (i | i) (j | j) <;> simp [K, Matrix.one_apply, e.injective.eq_iff]
  have hKdet : IsUnit K.det := by
    rwa [← det_submatrix_equiv_self e, hK, det_fromBlocks_zero₁₂, det_one, mul_one]
  refine ⟨GeneralLinearGroup.mk'' K hKdet, ?_⟩
  ext i j
  simp [K]

/-! ### Invertible matrices whose rows `e (p)` are those of the identity -/

section RowsEqOne

variable (e : m ⊕ p ≃ n) {g : GL n R}

/-- If the rows `e (p)` of an invertible matrix `g` are those of the identity matrix, so are the
rows `e (p)` of `g⁻¹`. -/
theorem inv_apply_of_rows_eq_one
    (hg : ∀ i j, (g : Matrix n n R) (e (.inr i)) j = (1 : Matrix n n R) (e (.inr i)) j)
    (i : p) (j : n) :
    (g : Matrix n n R)⁻¹ (e (.inr i)) j = (1 : Matrix n n R) (e (.inr i)) j := by
  have h1 : ((g : Matrix n n R) * (g : Matrix n n R)⁻¹) (e (.inr i)) j =
      (1 : Matrix n n R) (e (.inr i)) j := by
    rw [mul_nonsing_inv _ (isUnits_det_units g)]
  rw [Matrix.mul_apply] at h1
  simpa [hg, Matrix.one_apply] using h1

/-- If the rows `e (p)` of `g ∈ GL_n(R)` are those of the identity matrix, then `(k g)⁻¹` and `k⁻¹`
have the same rows `e (p)`. -/
theorem submatrix_inv_mul_of_rows_eq_one
    (hg : ∀ i j, (g : Matrix n n R) (e (.inr i)) j = (1 : Matrix n n R) (e (.inr i)) j)
    (k : GL n R) :
    (((k * g)⁻¹ : GL n R) : Matrix n n R).submatrix (e ∘ Sum.inr) id =
      ((k⁻¹ : GL n R) : Matrix n n R).submatrix (e ∘ Sum.inr) id := by
  rw [_root_.mul_inv_rev, GeneralLinearGroup.coe_mul, coe_units_inv, coe_units_inv]
  ext i j
  simp [Matrix.mul_apply, inv_apply_of_rows_eq_one e hg, Matrix.one_apply]

/-- If the rows `e (p)` of `g ∈ GL_n(R)` are those of the identity matrix, then the columns `e (m)`
of `k g` are those of `k` times the square block of `g` on `e (m)`. -/
theorem submatrix_mul_of_rows_eq_one [Fintype m]
    (hg : ∀ i j, (g : Matrix n n R) (e (.inr i)) j = (1 : Matrix n n R) (e (.inr i)) j)
    (k : GL n R) :
    ((k * g : GL n R) : Matrix n n R).submatrix id (e ∘ Sum.inl) =
      (k : Matrix n n R).submatrix id (e ∘ Sum.inl) *
        (g : Matrix n n R).submatrix (e ∘ Sum.inl) (e ∘ Sum.inl) := by
  have : Fintype p := Fintype.ofInjective (e ∘ Sum.inr) (e.injective.comp Sum.inr_injective)
  rw [GeneralLinearGroup.coe_mul]
  ext i j
  simp [Matrix.mul_apply, ← e.sum_comp, Fintype.sum_sum_type, hg]

/-- If the rows `e (p)` of `g ∈ GL_n(R)` are those of the identity matrix, then the determinant of
`g` is that of its square block on `e (m)`. -/
theorem det_eq_det_submatrix_of_rows_eq_one [Fintype m] [DecidableEq m]
    (hg : ∀ i j, (g : Matrix n n R) (e (.inr i)) j = (1 : Matrix n n R) (e (.inr i)) j) :
    (g : Matrix n n R).det = ((g : Matrix n n R).submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)).det := by
  classical
  have : Fintype p := Fintype.ofInjective (e ∘ Sum.inr) (e.injective.comp Sum.inr_injective)
  have hblocks : (g : Matrix n n R).submatrix e e =
      fromBlocks ((g : Matrix n n R).submatrix (e ∘ Sum.inl) (e ∘ Sum.inl))
        ((g : Matrix n n R).submatrix (e ∘ Sum.inl) (e ∘ Sum.inr)) 0 1 := by
    ext (i | i) (j | j) <;> simp [hg, Matrix.one_apply, e.injective.eq_iff]
  rw [← det_submatrix_equiv_self e, hblocks, det_fromBlocks_zero₂₁, det_one, mul_one]

/-- **Invertible matrices with the same rows of their inverses.** If `k⁻¹` and `k'⁻¹` have the same
rows `e (p)`, then the columns `e (m)` of `k'` are those of `k` times an invertible matrix `h`, and
`det k' = det k * det h`. -/
theorem exists_submatrix_eq_mul_of_submatrix_inv_eq [Fintype m] [DecidableEq m] {k k' : GL n R}
    (hkk' : ((k⁻¹ : GL n R) : Matrix n n R).submatrix (e ∘ Sum.inr) id =
      ((k'⁻¹ : GL n R) : Matrix n n R).submatrix (e ∘ Sum.inr) id) :
    ∃ h : GL m R, (k' : Matrix n n R).submatrix id (e ∘ Sum.inl) =
        (k : Matrix n n R).submatrix id (e ∘ Sum.inl) * (h : Matrix m m R) ∧
      (k' : Matrix n n R).det = (k : Matrix n n R).det * (h : Matrix m m R).det := by
  -- The rows `e (p)` of `k⁻¹ k'` are those of the identity.
  have hg (i : p) (j : n) : ((k⁻¹ * k' : GL n R) : Matrix n n R) (e (.inr i)) j =
      (1 : Matrix n n R) (e (.inr i)) j := by
    have hrow (l : n) : ((k⁻¹ : GL n R) : Matrix n n R) (e (.inr i)) l =
        ((k'⁻¹ : GL n R) : Matrix n n R) (e (.inr i)) l := by
      simpa using congrArg (fun M : Matrix p n R ↦ M i l) hkk'
    rw [GeneralLinearGroup.coe_mul, Matrix.mul_apply]
    simp_rw [hrow]
    rw [← Matrix.mul_apply, ← GeneralLinearGroup.coe_mul, inv_mul_cancel,
      GeneralLinearGroup.coe_one]
  have hyk := submatrix_mul_of_rows_eq_one e hg k
  have hdet := det_eq_det_submatrix_of_rows_eq_one e hg
  rw [mul_inv_cancel_left] at hyk
  refine ⟨GeneralLinearGroup.mk''
    (((k⁻¹ * k' : GL n R) : Matrix n n R).submatrix (e ∘ Sum.inl) (e ∘ Sum.inl))
    (hdet ▸ isUnits_det_units _), hyk, ?_⟩
  rw [GeneralLinearGroup.val_mk'', ← hdet, ← det_mul, ← GeneralLinearGroup.coe_mul,
    mul_inv_cancel_left]

end RowsEqOne

end Matrix.GeneralLinearGroup
