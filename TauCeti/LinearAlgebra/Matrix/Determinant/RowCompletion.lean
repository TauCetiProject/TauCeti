/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Determinants of complementary row completions

Completing a family of rows by the last rows of an inverse matrix gives a determinant
whose product with the determinant of that matrix is the determinant of the pairings
with its first columns. This compares determinant characters on row and column frames.
-/

public section

namespace Matrix

variable {R b a : Type*} [CommRing R] [Fintype b] [Fintype a]
  [DecidableEq b] [DecidableEq a]

/-- The determinant of `s` completed by the last rows of `k⁻¹`, multiplied by `det k`,
is the determinant of `s` paired with the first columns of `k`. -/
theorem det_fromRows_submatrix_inv_mul_det (s : Matrix b (b ⊕ a) R)
    (k : GeneralLinearGroup (b ⊕ a) R) :
    (fromRows s ((↑k⁻¹ : Matrix (b ⊕ a) (b ⊕ a) R).submatrix Sum.inr id)).det *
      (k : Matrix (b ⊕ a) (b ⊕ a) R).det =
      (s * (k : Matrix (b ⊕ a) (b ⊕ a) R).submatrix id Sum.inl).det := by
  have hbottom : (↑k⁻¹ : Matrix (b ⊕ a) (b ⊕ a) R).submatrix Sum.inr id *
      (k : Matrix (b ⊕ a) (b ⊕ a) R) =
      (1 : Matrix (b ⊕ a) (b ⊕ a) R).submatrix Sum.inr id := by
    simpa only [submatrix_id_id, Units.inv_mul] using
      (submatrix_mul (↑k⁻¹ : Matrix (b ⊕ a) (b ⊕ a) R)
        (k : Matrix (b ⊕ a) (b ⊕ a) R) Sum.inr id id Function.bijective_id).symm
  have hblocks : fromRows s ((↑k⁻¹ : Matrix (b ⊕ a) (b ⊕ a) R).submatrix Sum.inr id) *
      (k : Matrix (b ⊕ a) (b ⊕ a) R) = fromBlocks
        (s * (k : Matrix (b ⊕ a) (b ⊕ a) R).submatrix id Sum.inl)
        (s * (k : Matrix (b ⊕ a) (b ⊕ a) R).submatrix id Sum.inr) 0 1 := by
    rw [fromRows_mul, hbottom]
    -- The zero-block entry is definitionally zero after the block evaluation lemmas.
    ext (i | i) (j | j) <;>
      simp only [fromRows_apply_inl, fromRows_apply_inr, fromBlocks_apply₁₁,
        fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, submatrix_apply,
        id_eq, Matrix.mul_apply, Matrix.one_apply, Sum.inr.injEq,
        Sum.inr_ne_inl, ite_false]
    rfl
  simpa only [det_mul, det_fromBlocks_zero₂₁, det_one, mul_one] using congrArg det hblocks

end Matrix
