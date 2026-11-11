/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Determinants with entries in row ideals

Every term `sign σ * ∏ i, A i (σ i)` of the Leibniz expansion of a square determinant takes exactly
one factor from each row. So if every entry of row `i` lies in an ideal `J i`, the determinant lies
in the product ideal `∏ i, J i`, and symmetrically for columns. The common-ideal form puts the
determinant in `J ^ card n`, and the divisibility form says that if `r i` divides every entry of
row `i` then `∏ i, r i` divides the determinant. The exact identity behind the divisibility form,
that scaling row `i` by `r i` multiplies the determinant by `∏ i, r i`, is Mathlib's
`Matrix.det_mul_column`.

Each statement is applied to the full-row minors `det (A.submatrix id c)` of a rectangular matrix
`A`, for an arbitrary column choice `c`; nothing requires `c` to be injective.

The empty product of ideals is `⊤`, which contains the determinant `1` of a `0 × 0` matrix, so no
statement needs the index type to be nonempty.

## Main results

* `Matrix.det_mem_prod_row_ideals`, `Matrix.det_mem_prod_col_ideals`: the determinant lies in the
  product of the row ideals, and of the column ideals.
* `Matrix.det_mem_pow_card`: the determinant of a matrix with all entries in `J` lies in
  `J ^ card n`.
* `Matrix.prod_dvd_det_of_dvd_row`, `Matrix.pow_card_dvd_det`: row divisors multiply to a divisor
  of the determinant, and a common divisor `r` of all entries gives `r ^ card n ∣ det A`.
* `Matrix.det_submatrix_mem_prod_row_ideals` and its companions: the same statements for every
  full-row minor of a rectangular matrix.

## References

* S. Treil, *Linear Algebra Done Wrong*, Chapter 3, formula (4.2): every term of the expansion
  contains exactly one entry from each row and each column.
-/

public section

namespace Matrix

open Finset

variable {m n R : Type*} [CommRing R] [Fintype m] [DecidableEq m]

/-- **Determinants lie in the product of the row ideals.** If every entry of row `i` lies in the
ideal `J i`, then `det A ∈ ∏ i, J i`. The empty product is `⊤`. -/
theorem det_mem_prod_row_ideals (A : Matrix m m R) (J : m → Ideal R) (h : ∀ i j, A i j ∈ J i) :
    A.det ∈ ∏ i, J i := by
  rw [← det_transpose, det_apply']
  exact sum_mem fun σ _ ↦
    Ideal.mul_mem_left _ _ (Ideal.prod_mem_prod fun i _ ↦ h i (σ i))

/-- **Determinants lie in the product of the column ideals.** If every entry of column `j` lies in
the ideal `J j`, then `det A ∈ ∏ j, J j`. -/
theorem det_mem_prod_col_ideals (A : Matrix m m R) (J : m → Ideal R) (h : ∀ i j, A i j ∈ J j) :
    A.det ∈ ∏ j, J j := by
  rw [← det_transpose]
  exact det_mem_prod_row_ideals Aᵀ J fun i j ↦ h j i

/-- **Common-ideal form.** If every entry of a square matrix lies in `J`, its determinant lies in
`J ^ card m`. -/
theorem det_mem_pow_card (A : Matrix m m R) {J : Ideal R} (h : ∀ i j, A i j ∈ J) :
    A.det ∈ J ^ Fintype.card m := by
  simpa using det_mem_prod_row_ideals A (fun _ ↦ J) h

/-- **Row-divisor form.** If `r i` divides every entry of row `i`, then `∏ i, r i` divides the
determinant. -/
theorem prod_dvd_det_of_dvd_row (A : Matrix m m R) (r : m → R) (h : ∀ i j, r i ∣ A i j) :
    ∏ i, r i ∣ A.det := by
  simpa [← Ideal.mem_span_singleton, ← Ideal.prod_span_singleton] using
    det_mem_prod_row_ideals A (fun i ↦ Ideal.span {r i}) fun i j ↦
      Ideal.mem_span_singleton.2 (h i j)

/-- **Principal form.** If `r` divides every entry of a square matrix, then `r ^ card m` divides
its determinant. -/
theorem pow_card_dvd_det (A : Matrix m m R) {r : R} (h : ∀ i j, r ∣ A i j) :
    r ^ Fintype.card m ∣ A.det := by
  simpa using prod_dvd_det_of_dvd_row A (fun _ ↦ r) h

/-! ### Full-row minors of rectangular matrices -/

/-- Every full-row minor of a rectangular matrix whose row `i` has entries in `J i` lies in
`∏ i, J i`. -/
theorem det_submatrix_mem_prod_row_ideals (A : Matrix m n R) (J : m → Ideal R)
    (h : ∀ i j, A i j ∈ J i) (c : m → n) : (A.submatrix id c).det ∈ ∏ i, J i :=
  det_mem_prod_row_ideals _ J fun i j ↦ h i (c j)

/-- If column `j` of a rectangular matrix has entries in `J j`, the full-row minor on the columns
`c` lies in `∏ i, J (c i)`. -/
theorem det_submatrix_mem_prod_col_ideals (A : Matrix m n R) (J : n → Ideal R)
    (h : ∀ i j, A i j ∈ J j) (c : m → n) : (A.submatrix id c).det ∈ ∏ i, J (c i) :=
  det_mem_prod_col_ideals _ (J ∘ c) fun i j ↦ h i (c j)

/-- Every full-row minor of a rectangular matrix with entries in `J` lies in `J ^ card m`. -/
theorem det_submatrix_mem_pow_card (A : Matrix m n R) {J : Ideal R} (h : ∀ i j, A i j ∈ J)
    (c : m → n) : (A.submatrix id c).det ∈ J ^ Fintype.card m :=
  det_mem_pow_card _ fun i j ↦ h i (c j)

/-- If `r i` divides every entry of row `i` of a rectangular matrix, then `∏ i, r i` divides every
full-row minor. -/
theorem prod_dvd_det_submatrix_of_dvd_row (A : Matrix m n R) (r : m → R)
    (h : ∀ i j, r i ∣ A i j) (c : m → n) : ∏ i, r i ∣ (A.submatrix id c).det :=
  prod_dvd_det_of_dvd_row _ r fun i j ↦ h i (c j)

/-- If `r` divides every entry of a rectangular matrix, then `r ^ card m` divides every full-row
minor. -/
theorem pow_card_dvd_det_submatrix (A : Matrix m n R) {r : R} (h : ∀ i j, r ∣ A i j)
    (c : m → n) : r ^ Fintype.card m ∣ (A.submatrix id c).det :=
  pow_card_dvd_det _ fun i j ↦ h i (c j)

end Matrix
