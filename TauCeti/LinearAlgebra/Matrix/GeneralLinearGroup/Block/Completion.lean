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

## Main results

* `Matrix.GeneralLinearGroup.exists_submatrix_comp_inr_id_eq_of_isUnit_det`: a block of rows
  with an invertible square block is the block of rows of an invertible matrix.
* `Matrix.GeneralLinearGroup.exists_submatrix_id_comp_inl_eq_of_isUnit_det`: a block of columns
  with an invertible square block is the block of columns of an invertible matrix.
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

end Matrix.GeneralLinearGroup
