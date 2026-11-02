/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Hermite normal form of integer matrices

An `m × k` integer matrix `H` is in (column-style, upper) *Hermite normal form* if there is a
strictly increasing map `p : Fin k → Fin m`, the *pivot rows*, such that for every column `j`

* the pivot `H (p j) j` is positive;
* every entry of column `j` below the pivot vanishes, so the pivot is the lowest nonzero entry of
  its column;
* every entry `H (p j) j'` to the right of the pivot, in a column `j < j'`, is reduced modulo the
  pivot: `0 ≤ H (p j) j' < H (p j) j`.

Columns generate the lattice, as in Mathlib's `Matrix.mulVec` and `Basis.toMatrix` conventions, and
a matrix in Hermite normal form has no zero column, so `k` is the rank of its column lattice. This
is the normal form of integer lattices under unimodular column operations, the standard way to
record and compare sublattices of `ℤ^m` and ideals of number fields in a fixed integral basis.
This file sets up the predicate and its elementary structure: the pivots are determined by the
matrix, the columns are independent, and a square matrix in this form is triangular with positive
determinant.

## Main definitions

* `Matrix.IsHermitePivotedBy H p`: `H` is in Hermite normal form with pivot rows `p`.
* `Matrix.IsHermiteNormalForm H`: `H` is in Hermite normal form for some pivot rows.

## Main results

* `Matrix.IsHermitePivotedBy.isGreatest`: the pivot row of column `j` is the largest row with a
  nonzero entry in column `j`; hence `Matrix.IsHermiteNormalForm.pivot_unique`: the pivot rows are
  determined by `H`.
* `Matrix.IsHermiteNormalForm.linearIndependent_cols`: the columns of `H` are `ℤ`-linearly
  independent.
* `Matrix.IsHermiteNormalForm.isUpperTriangular`, `Matrix.IsHermiteNormalForm.diag_pos`: a square
  matrix in Hermite normal form is upper triangular with positive diagonal;
  `Matrix.IsHermiteNormalForm.det_eq_prod_diag` and `Matrix.IsHermiteNormalForm.det_pos`: so its
  determinant is the product of the pivots, and is positive.
* `Matrix.IsHermiteNormalForm.one`: the identity matrix is in Hermite normal form.
* `Matrix.isHermitePivotedBy_of_succ`, `Matrix.isHermitePivotedBy_cons`: a matrix in Hermite normal
  form extends to one with an extra top row, and also with an extra first column whose pivot is in
  the top row.

## References

* Daniele Micciancio, *CSE 206A: Lattice Algorithms and Applications*, lecture 1, Definition 7
  (the square nonsingular case, with the same orientation).
* Henri Cohen, *A Course in Computational Algebraic Number Theory*, §2.4.2, and Karim Belabas,
  *Topics in computational algebraic number theory*, §4.3: the column-style upper convention used
  for ideals of number fields.
-/

public section

namespace Matrix

variable {m k : ℕ} {H : Matrix (Fin m) (Fin k) ℤ} {p p' : Fin k → Fin m}

/-- `H` is in (column-style, upper) Hermite normal form with pivot rows `p`: the pivot rows
increase strictly, each pivot `H (p j) j` is positive and is the lowest nonzero entry of its
column, and each entry to the right of a pivot in its row is reduced modulo that pivot. -/
structure IsHermitePivotedBy (H : Matrix (Fin m) (Fin k) ℤ) (p : Fin k → Fin m) : Prop where
  /-- The pivot rows increase strictly from left to right. -/
  strictMono : StrictMono p
  /-- Each pivot is positive. -/
  pivot_pos (j : Fin k) : 0 < H (p j) j
  /-- Every entry below a pivot vanishes. -/
  eq_zero_of_lt (j : Fin k) {i : Fin m} : p j < i → H i j = 0
  /-- Entries to the right of a pivot in its row are nonnegative. -/
  nonneg_of_lt {j j' : Fin k} : j < j' → 0 ≤ H (p j) j'
  /-- Entries to the right of a pivot in its row are smaller than the pivot. -/
  lt_pivot_of_lt {j j' : Fin k} : j < j' → H (p j) j' < H (p j) j

/-- An integer matrix is in (column-style, upper) Hermite normal form if it is in Hermite normal
form for some strictly increasing choice of pivot rows, see `Matrix.IsHermitePivotedBy`. -/
def IsHermiteNormalForm (H : Matrix (Fin m) (Fin k) ℤ) : Prop :=
  ∃ p, H.IsHermitePivotedBy p

/-- A matrix is in Hermite normal form exactly when it is so for some pivot rows. -/
theorem isHermiteNormalForm_iff : H.IsHermiteNormalForm ↔ ∃ p, H.IsHermitePivotedBy p :=
  Iff.rfl

/-- A matrix in Hermite normal form with given pivot rows is in Hermite normal form. -/
theorem IsHermitePivotedBy.isHermiteNormalForm (h : H.IsHermitePivotedBy p) :
    H.IsHermiteNormalForm :=
  ⟨p, h⟩

namespace IsHermitePivotedBy

/-- Each pivot is nonzero. -/
theorem pivot_ne_zero (h : H.IsHermitePivotedBy p) (j : Fin k) : H (p j) j ≠ 0 :=
  (h.pivot_pos j).ne'

/-- The pivot row of a column is the largest row with a nonzero entry in that column. -/
theorem isGreatest (h : H.IsHermitePivotedBy p) (j : Fin k) :
    IsGreatest {i | H i j ≠ 0} (p j) :=
  ⟨h.pivot_ne_zero j, fun _ hi ↦ not_lt.mp fun hlt ↦ hi (h.eq_zero_of_lt j hlt)⟩

/-- The pivot rows of a matrix in Hermite normal form are unique. -/
theorem unique (h : H.IsHermitePivotedBy p) (h' : H.IsHermitePivotedBy p') : p = p' :=
  funext fun j ↦ (h.isGreatest j).unique (h'.isGreatest j)

/-- The rows of `H` at its pivots form an upper triangular square matrix, whose diagonal entries
are the pivots. -/
theorem isUpperTriangular_submatrix (h : H.IsHermitePivotedBy p) :
    (H.submatrix p id).IsUpperTriangular :=
  fun _ _ hlt ↦ h.eq_zero_of_lt _ (h.strictMono hlt)

/-- The columns of a matrix in Hermite normal form are `ℤ`-linearly independent. -/
theorem linearIndependent_cols (h : H.IsHermitePivotedBy p) : LinearIndependent ℤ H.col := by
  refine mulVec_injective_iff.mp <| (injective_iff_map_eq_zero H.mulVecLin).mpr fun v hv ↦ ?_
  have hdet : (H.submatrix p id).det ≠ 0 :=
    h.isUpperTriangular_submatrix.det_ne_zero_iff.mpr h.pivot_ne_zero
  -- The pivot rows of `H *ᵥ v` are the entries of `(H.submatrix p id) *ᵥ v`.
  exact eq_zero_of_mulVec_eq_zero hdet (funext fun j ↦ congrFun hv (p j))

/-- For a square matrix the pivot rows are the identity. -/
theorem eq_id {H : Matrix (Fin m) (Fin m) ℤ} {p : Fin m → Fin m} (h : H.IsHermitePivotedBy p) :
    p = id :=
  h.strictMono.eq_id

end IsHermitePivotedBy

/-- The identity matrix is in Hermite normal form with the identity as pivot rows. -/
theorem isHermitePivotedBy_one : (1 : Matrix (Fin m) (Fin m) ℤ).IsHermitePivotedBy id where
  strictMono := strictMono_id
  pivot_pos j := by rw [id_eq, one_apply_eq]; exact one_pos
  eq_zero_of_lt _ _ hlt := one_apply_ne' hlt.ne
  nonneg_of_lt hlt := (one_apply_ne hlt.ne).ge
  lt_pivot_of_lt hlt := by rw [id_eq, one_apply_eq, one_apply_ne hlt.ne]; exact one_pos

namespace IsHermiteNormalForm

/-- The pivot rows of a matrix in Hermite normal form are determined by the matrix. -/
theorem pivot_unique (hH : H.IsHermiteNormalForm) : ∃! p, H.IsHermitePivotedBy p :=
  let ⟨p, h⟩ := hH
  ⟨p, h, fun _ h' ↦ h'.unique h⟩

/-- The columns of a matrix in Hermite normal form are `ℤ`-linearly independent. -/
theorem linearIndependent_cols (hH : H.IsHermiteNormalForm) : LinearIndependent ℤ H.col :=
  let ⟨_, h⟩ := hH
  h.linearIndependent_cols

/-- A square matrix in Hermite normal form is in Hermite normal form with the identity as pivot
rows. -/
theorem isHermitePivotedBy_id {H : Matrix (Fin m) (Fin m) ℤ} (hH : H.IsHermiteNormalForm) :
    H.IsHermitePivotedBy id :=
  let ⟨_, h⟩ := hH
  h.eq_id ▸ h

variable {H : Matrix (Fin m) (Fin m) ℤ}

/-- A square matrix in Hermite normal form is upper triangular. -/
theorem isUpperTriangular (hH : H.IsHermiteNormalForm) : H.IsUpperTriangular := by
  simpa using hH.isHermitePivotedBy_id.isUpperTriangular_submatrix

/-- A square matrix in Hermite normal form has positive diagonal entries. -/
theorem diag_pos (hH : H.IsHermiteNormalForm) (i : Fin m) : 0 < H i i :=
  hH.isHermitePivotedBy_id.pivot_pos i

/-- The determinant of a square matrix in Hermite normal form is the product of its pivots. -/
theorem det_eq_prod_diag (hH : H.IsHermiteNormalForm) : H.det = ∏ i, H i i :=
  det_of_isUpperTriangular hH.isUpperTriangular

/-- A square matrix in Hermite normal form has positive determinant. -/
theorem det_pos (hH : H.IsHermiteNormalForm) : 0 < H.det := by
  rw [hH.det_eq_prod_diag]
  exact Finset.prod_pos fun i _ ↦ hH.diag_pos i

/-- The identity matrix is in Hermite normal form. -/
theorem one : (1 : Matrix (Fin m) (Fin m) ℤ).IsHermiteNormalForm :=
  isHermitePivotedBy_one.isHermiteNormalForm

end IsHermiteNormalForm

/-- A matrix with no columns is in Hermite normal form; its column lattice is zero. -/
theorem isHermiteNormalForm_of_fin_zero (H : Matrix (Fin m) (Fin 0) ℤ) : H.IsHermiteNormalForm :=
  ⟨Fin.elim0, fun j ↦ j.elim0, fun j ↦ j.elim0, fun j ↦ j.elim0, fun {j} ↦ j.elim0,
    fun {j} ↦ j.elim0⟩

/-! ### Adding a top row -/

/-- If deleting the top row of `H` leaves a matrix `H'` in Hermite normal form with pivot rows
`p`, then `H` is in Hermite normal form with pivot rows `Fin.succ ∘ p`, whatever its top row. -/
theorem isHermitePivotedBy_of_succ {H' : Matrix (Fin m) (Fin k) ℤ} {p : Fin k → Fin m}
    (h : H'.IsHermitePivotedBy p) {H : Matrix (Fin (m + 1)) (Fin k) ℤ}
    (hH : ∀ (i : Fin m) (j : Fin k), H i.succ j = H' i j) :
    H.IsHermitePivotedBy (Fin.succ ∘ p) where
  strictMono := Fin.strictMono_succ.comp h.strictMono
  pivot_pos j := by simpa [hH] using h.pivot_pos j
  eq_zero_of_lt j {i} hi := by
    cases i using Fin.cases with
    | zero => exact absurd hi (Fin.not_lt_zero _)
    | succ i => rw [hH]; exact h.eq_zero_of_lt j (Fin.succ_lt_succ_iff.mp hi)
  nonneg_of_lt hjj' := by simpa [hH] using h.nonneg_of_lt hjj'
  lt_pivot_of_lt hjj' := by simpa [hH] using h.lt_pivot_of_lt hjj'

/-- Let `H` have a positive top left entry `H 0 0`, zeros below it, top row entries reduced modulo
`H 0 0`, and, after deleting the top row and the first column, a matrix `H'` in Hermite normal
form with pivot rows `p`. Then `H` is in Hermite normal form, with pivot rows `0` followed by
`Fin.succ ∘ p`. -/
theorem isHermitePivotedBy_cons {H' : Matrix (Fin m) (Fin k) ℤ} {p : Fin k → Fin m}
    (h : H'.IsHermitePivotedBy p) {H : Matrix (Fin (m + 1)) (Fin (k + 1)) ℤ}
    (h₀ : 0 < H 0 0) (hcol : ∀ i : Fin m, H i.succ 0 = 0)
    (hH : ∀ (i : Fin m) (j : Fin k), H i.succ j.succ = H' i j)
    (hrow : ∀ j : Fin k, 0 ≤ H 0 j.succ ∧ H 0 j.succ < H 0 0) :
    H.IsHermitePivotedBy (Fin.cons 0 (Fin.succ ∘ p)) where
  strictMono := Fin.strictMono_cons.mpr
    ⟨fun _ ↦ Fin.succ_pos _, Fin.strictMono_succ.comp h.strictMono⟩
  pivot_pos j := by
    cases j using Fin.cases with
    | zero => exact h₀
    | succ j => simpa [hH] using h.pivot_pos j
  eq_zero_of_lt j {i} hi := by
    cases i using Fin.cases with
    | zero => exact absurd hi (Fin.not_lt_zero _)
    | succ i =>
      cases j using Fin.cases with
      | zero => exact hcol i
      | succ j => rw [hH]; exact h.eq_zero_of_lt j (by simpa using hi)
  nonneg_of_lt {j j'} hjj' := by
    cases j' using Fin.cases with
    | zero => exact absurd hjj' (Fin.not_lt_zero _)
    | succ j' =>
      cases j using Fin.cases with
      | zero => exact (hrow j').1
      | succ j => simpa [hH] using h.nonneg_of_lt (Fin.succ_lt_succ_iff.mp hjj')
  lt_pivot_of_lt {j j'} hjj' := by
    cases j' using Fin.cases with
    | zero => exact absurd hjj' (Fin.not_lt_zero _)
    | succ j' =>
      cases j using Fin.cases with
      | zero => exact (hrow j').2
      | succ j => simpa [hH] using h.lt_pivot_of_lt (Fin.succ_lt_succ_iff.mp hjj')

/-! ### Examples -/

/-- The matrix with columns `(3, 0)` and `(2, 1)` is in Hermite normal form. -/
example : !![(3 : ℤ), 2; 0, 1].IsHermiteNormalForm :=
  ⟨id, strictMono_id, by decide, by decide, by decide, by decide⟩

/-- The matrix with columns `(3, 0)` and `(4, 1)` is not in Hermite normal form: the entry `4` is
not reduced modulo the pivot `3`. -/
example : ¬ !![(3 : ℤ), 4; 0, 1].IsHermiteNormalForm := fun hH ↦
  absurd (hH.isHermitePivotedBy_id.lt_pivot_of_lt (j := 0) (j' := 1) (by decide)) (by decide)

/-- The matrix `diag(2, -1)` is not in Hermite normal form: the pivot `-1` is negative. -/
example : ¬ !![(2 : ℤ), 0; 0, -1].IsHermiteNormalForm := fun hH ↦
  absurd (hH.diag_pos 1) (by decide)

end Matrix
