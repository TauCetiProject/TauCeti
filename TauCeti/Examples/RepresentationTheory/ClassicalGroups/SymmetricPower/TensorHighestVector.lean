/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.SymmetricPower.TensorHighestVector

/-!
# Highest weight vectors of tensor products of binary forms in small degree

Checks of `TauCeti.RepresentationTheory.ClassicalGroups.SymmetricPower.TensorHighestVector` in two
integer variables `x = X 0` and `y = X 1`.

* For `m = n = 0` the highest weight vector is `1 ⊗ 1`, not the zero vector.
* For `m = n = 1` and `r = 0` it is `x ⊗ x`; for `r = 1` it is `x ⊗ y - y ⊗ x`, with a minus sign.
* For `r > min m n` it is zero, and for `r ≤ min m n` it is nonzero.
* The upper unipotent matrix `!![1, 1; 0, 1]` fixes `x ⊗ y - y ⊗ x`, and `diag(2, 3)` multiplies it
  by `6`, the weight `(1, 1)`.
-/

public section

open MvPolynomial Matrix
open scoped TensorProduct

namespace TauCeti.Examples

/-- For `m = n = 0` the highest weight vector is `1 ⊗ 1`. -/
example : polynomialTensorHighest ℤ 0 0 0 = 1 := by
  simp [Algebra.TensorProduct.one_def]

/-- For `m = n = 1` and `r = 0` the highest weight vector is `x ⊗ x`. -/
example : polynomialTensorHighest ℤ 1 1 0 = X 0 ⊗ₜ X 0 := by
  simp

/-- For `m = n = 1` and `r = 1` the highest weight vector is `x ⊗ y - y ⊗ x`. -/
example : polynomialTensorHighest ℤ 1 1 1 = X 0 ⊗ₜ X 1 - X 1 ⊗ₜ X 0 := by
  simp [polynomialTensorHighest_of_le, ← Algebra.TensorProduct.one_def]

/-- For `m = 0` there is no highest weight vector with `r = 1`. -/
example : polynomialTensorHighest ℤ 0 2 1 = 0 :=
  polynomialTensorHighest_of_not_le (by norm_num)

/-- For `m = 1` and `n = 2` the highest weight vector with `r = 1` is nonzero. -/
example : polynomialTensorHighest ℤ 1 2 1 ≠ 0 :=
  polynomialTensorHighest_ne_zero (by norm_num) (by norm_num)

/-- The upper unipotent matrix `!![1, 1; 0, 1]` fixes `x ⊗ y - y ⊗ x`. -/
example : Algebra.TensorProduct.map (polynomialAction !![(1 : ℤ), 1; 0, 1])
    (polynomialAction !![(1 : ℤ), 1; 0, 1]) (polynomialTensorHighest ℤ 1 1 1) =
      polynomialTensorHighest ℤ 1 1 1 :=
  map_polynomialAction_unipotent_polynomialTensorHighest 1

/-- The diagonal matrix `diag(2, 3)` multiplies `x ⊗ y - y ⊗ x` by `2 * 3 = 6`. -/
example : Algebra.TensorProduct.map (polynomialAction (diagonal ![(2 : ℤ), 3]))
    (polynomialAction (diagonal ![(2 : ℤ), 3])) (polynomialTensorHighest ℤ 1 1 1) =
      (6 : ℤ) • polynomialTensorHighest ℤ 1 1 1 := by
  rw [map_polynomialAction_diagonal_polynomialTensorHighest]
  norm_num

end TauCeti.Examples
