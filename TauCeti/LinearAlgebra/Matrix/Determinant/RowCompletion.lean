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
theorem det_fromRows_toRows₂_inv_mul_det (s : Matrix b (b ⊕ a) R)
    (k : GeneralLinearGroup (b ⊕ a) R) :
    (fromRows s ((↑k⁻¹ : Matrix (b ⊕ a) (b ⊕ a) R).toRows₂)).det *
      (k : Matrix (b ⊕ a) (b ⊕ a) R).det =
      (s * (k : Matrix (b ⊕ a) (b ⊕ a) R).toCols₁).det := by
  have hbottom : (↑k⁻¹ : Matrix (b ⊕ a) (b ⊕ a) R).toRows₂ *
      (k : Matrix (b ⊕ a) (b ⊕ a) R) =
      (1 : Matrix (b ⊕ a) (b ⊕ a) R).toRows₂ := by
    ext i j
    simpa [Matrix.mul_apply] using congrArg
      (fun M : Matrix (b ⊕ a) (b ⊕ a) R ↦ M (Sum.inr i) j) (Units.inv_mul k)
  have hblocks : fromRows s ((↑k⁻¹ : Matrix (b ⊕ a) (b ⊕ a) R).toRows₂) *
      (k : Matrix (b ⊕ a) (b ⊕ a) R) = fromBlocks
        (s * (k : Matrix (b ⊕ a) (b ⊕ a) R).toCols₁)
        (s * (k : Matrix (b ⊕ a) (b ⊕ a) R).toCols₂) 0 1 := by
    rw [fromRows_mul, hbottom]
    ext (i | i) (j | j) <;> simp [Matrix.mul_apply, Matrix.one_apply]
  simpa only [det_mul, det_fromBlocks_zero₂₁, det_one, mul_one] using congrArg det hblocks

end Matrix
