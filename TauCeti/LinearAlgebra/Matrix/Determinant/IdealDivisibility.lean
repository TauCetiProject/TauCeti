/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Ideal.Operations
import TauCeti.LinearAlgebra.Determinant.Basic

/-!
# Determinants with entries in row ideals

Every term `sign σ * ∏ i, A i (σ i)` of the Leibniz expansion of a square determinant takes exactly
one factor from each row. So if every entry of row `i` lies in an ideal `J i`, the determinant lies
in the product ideal `∏ i, J i`, and symmetrically for columns; conversely, the determinants with
rows in the `J i` generate `∏ i, J i`, already through diagonal matrices. The common-ideal form
puts the determinant in `J ^ card n`, and the divisibility form says that if `r i` divides every
entry of row `i` then `∏ i, r i` divides the determinant. The exact identity behind the
divisibility form, that scaling row `i` by `r i` multiplies the determinant by `∏ i, r i`, is
Mathlib's `Matrix.det_mul_column`.

Each membership and divisibility statement is applied to the full-row minors
`det (A.submatrix id c)` of a rectangular matrix `A`, for an arbitrary column choice `c`; nothing
requires `c` to be injective. The generation statement `Matrix.span_det_eq_prod_row_ideals` is
only stated for square matrices.

The empty product of ideals is `⊤`, which contains the determinant `1` of a `0 × 0` matrix, so no
statement needs the index type to be nonempty.

By multilinearity of the determinant in its columns, the determinant of an `R`-linear combination
`∑ i, s i • G i` of matrices lies in an ideal `P` whenever every matrix formed by picking each
column `j` from some `G (f j)` has determinant in `P`.

## Main results

* `Matrix.det_mem_prod_row_ideals`, `Matrix.det_mem_prod_col_ideals`: the determinant lies in the
  product of the row ideals, and of the column ideals.
* `Matrix.span_det_eq_prod_row_ideals`: these determinants generate the product of the row
  ideals.
* `Matrix.det_mem_pow_card`: the determinant of a matrix with all entries in `J` lies in
  `J ^ card n`.
* `Matrix.prod_dvd_det_of_dvd_row`, `Matrix.prod_mul_prod_dvd_det_of_dvd`,
  `Matrix.pow_card_dvd_det`: row divisors (and combined row-and-column divisors) multiply to a
  divisor of the determinant, and a common divisor `r` of all entries gives `r ^ card n ∣ det A`.
* `Matrix.det_submatrix_mem_prod_row_ideals` and its companions: the membership and
  divisibility statements for every full-row minor of a rectangular matrix.
* `Matrix.dvd_det_of_forall_row_mem_span`: if every row of a square matrix `N` lies in the row span
  of `M`, any common divisor of the full-column minors of `M` divides `N.det`.
* `Matrix.det_sum_smul_mem_of_forall_det_mem`: the determinant of `∑ i, s i • G i` lies in an
  ideal `P` whenever every column-selection matrix `of fun r j ↦ G (f j) r j` has determinant in
  `P`.

## References

* S. Treil, *Linear Algebra Done Wrong*, Chapter 3, formula (4.2): every term of the expansion
  contains exactly one entry from each row and each column.
* The row-span determinant divisibility theorem is adapted from `grh-lean`,
  `src/Lib/General/Algebra/SharpMinors.lean`
  (Copyright 2026 Anthropic, PBC, Apache 2.0).
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

open scoped Pointwise in
/-- **Row ideals generate their product.** The determinants of the square matrices whose `i`-th
row has entries in `J i` generate the product ideal `∏ i, J i`: diagonal matrices already give
every product `∏ i, x i` with `x i ∈ J i`. -/
theorem span_det_eq_prod_row_ideals (J : m → Ideal R) :
    Ideal.span {d | ∃ A : Matrix m m R, (∀ i j, A i j ∈ J i) ∧ A.det = d} = ∏ i, J i := by
  refine le_antisymm (Ideal.span_le.mpr ?_) ?_
  · rintro _ ⟨A, hA, rfl⟩
    exact det_mem_prod_row_ideals A J hA
  · calc ∏ i, J i = ∏ i, Ideal.span (J i : Set R) := by simp only [Ideal.span_eq]
      _ = Ideal.span (∏ i, (J i : Set R)) := Ideal.prod_span _ _
      _ ≤ _ := Ideal.span_mono fun x hx ↦ by
        obtain ⟨g, hg, rfl⟩ := (Set.mem_fintype_prod _ x).mp hx
        refine ⟨diagonal g, fun i j ↦ ?_, det_diagonal⟩
        by_cases hij : i = j
        · simpa [hij] using hg j
        · simp [diagonal_apply_ne _ hij]

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

/-- **Row-and-column-divisor form.** If `r i * c j` divides entry `(i, j)` of `A`, then
`(∏ i, r i) * (∏ j, c j)` divides `A.det`. -/
theorem prod_mul_prod_dvd_det_of_dvd (A : Matrix m m R) (r c : m → R)
    (h : ∀ i j, r i * c j ∣ A i j) :
    (∏ i, r i) * (∏ j, c j) ∣ A.det := by
  choose M hM using h
  have hmat : A = Matrix.diagonal r * Matrix.of M * Matrix.diagonal c := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply, hM i j]
    ring
  rw [hmat, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
  exact ⟨(Matrix.of M).det, by ring⟩

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

/-- **Determinant of a linear combination of matrices in an ideal.** If every matrix assembled by
choosing column `j` from `G (f j)` has determinant in an ideal `P`, then the determinant of any
`R`-linear combination `∑ i, s i • G i` also lies in `P`. -/
theorem det_sum_smul_mem_of_forall_det_mem {ι : Type*} [Fintype ι] {P : Ideal R} {s : ι → R}
    {G : ι → Matrix m m R} (hcol : ∀ f : m → ι, (of fun i j ↦ G (f j) i j).det ∈ P) :
    (∑ i : ι, s i • G i).det ∈ P := by
  rw [← det_transpose]
  have h_rows : (∑ i : ι, s i • G i)ᵀ = fun j : m ↦ ∑ i : ι, s i • (G i)ᵀ j :=
    funext₂ fun j l ↦ by simp [Matrix.sum_apply, Finset.sum_apply]
  rw [h_rows]
  -- `Matrix.det` is definitionally `detRowAlternating` applied to the rows of the matrix.
  change detRowAlternating (fun j : m ↦ ∑ i : ι, s i • (G i)ᵀ j) ∈ P
  rw [← AlternatingMap.coe_multilinearMap, MultilinearMap.map_sum]
  refine sum_mem fun f _ ↦ ?_
  rw [MultilinearMap.map_smul_univ]
  refine P.smul_mem _ ?_
  have h_mem := hcol f
  rwa [← det_transpose] at h_mem

/-- If every row of a square matrix `N` lies in the row span of a matrix `M`, then any common
divisor `x` of the full-column minors `(M.submatrix f id).det` divides `N.det`. -/
theorem dvd_det_of_forall_row_mem_span {M : Matrix n m R} {N : Matrix m m R} {x : R}
    (h_minor : ∀ f : m → n, x ∣ (M.submatrix f id).det)
    (h_row : ∀ i : m, N.row i ∈ Submodule.span R (Set.range M.row)) : x ∣ N.det := by
  rw [← Ideal.mem_span_singleton]
  have h := TauCeti.det_mem_of_mem_span (I := Ideal.span {x})
    (fun j : m ↦ LinearMap.proj (R := R) j) h_row fun w hw ↦ by
      choose f hf using hw
      have hM : (Matrix.of fun i j ↦ w i j) = M.submatrix f id := by
        ext i j
        exact congrFun (hf i).symm j
      simpa [hM, Ideal.mem_span_singleton] using h_minor f
  have hN : (Matrix.of fun i j ↦ N i j) = N := by ext i j; simp
  simpa [hN] using h

end Matrix
