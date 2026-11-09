/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Basic determinant formulas

Additions to Mathlib's `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`.

Mathlib computes the determinant of a matrix indexed by a singleton type (`Matrix.det_unique`)
and of a `Fin 2`-indexed matrix (`Matrix.det_fin_two`). A two-by-two matrix also arises indexed
by `m ⊕ n` with `m` and `n` singletons, for instance as `fromBlocks` of four `1 × 1` blocks or on
the `l ⊕ l` index of the standard symplectic form `Matrix.J l R`. `Matrix.det_sum_unique` gives
its determinant in coordinates, so that such a matrix need not be reindexed along `Fin 2` by hand.

If every row of a matrix `B` with `n + 2` rows and `n + 1` columns sums to `1`, then deleting the
rows of `B` one at a time gives `n + 2` square matrices, and the alternating sum of their
determinants vanishes. Indeed, it is the expansion along the first column of the square matrix
obtained from `B` by adjoining a first column of ones, and that column is the sum of the others.

A first column of ones also lets a square matrix drop one size: subtracting each row from its
successor (`Matrix.det_eq_of_forall_row_eq_smul_add_pred`) leaves a single `1` in that column, and
expanding along it (`Matrix.det_succ_column_zero`) leaves the matrix of consecutive row
differences of the remaining columns.

## Main results

* `Matrix.det_sum_unique`: the determinant of a matrix on `m ⊕ n`, for singletons `m` and `n`.
* `Matrix.sum_neg_one_pow_mul_det_submatrix_succAbove_eq_zero`: the alternating sum of the maximal
  minors of a matrix with `n + 2` rows and `n + 1` columns whose rows sum to `1` vanishes.
* `Matrix.det_eq_det_of_col_zero_eq_one`: a square matrix whose first column is constant `1` has
  the determinant of its consecutive row differences on the remaining columns.
-/

public section

namespace Matrix

variable {m n R : Type*} [Unique m] [Unique n] [DecidableEq m] [DecidableEq n] [Fintype m]
  [Fintype n] [CommRing R]

/-- The determinant of a matrix indexed by `m ⊕ n`, for singleton types `m` and `n`, is the
two-by-two determinant of its entries. -/
theorem det_sum_unique (A : Matrix (m ⊕ n) (m ⊕ n) R) :
    A.det = A (Sum.inl default) (Sum.inl default) * A (Sum.inr default) (Sum.inr default)
      - A (Sum.inl default) (Sum.inr default) * A (Sum.inr default) (Sum.inl default) := by
  -- Reindex along `Fin 2 ≃ m ⊕ n`. It sends `0` to `Sum.inl default` and `1` to `Sum.inr default`
  -- by definition, so `det_fin_two` is the claim up to `rfl`; `simp` cannot see through the
  -- numerals `0, 1 : Fin 2` to evaluate `finSumFinEquiv.symm` on them.
  rw [← det_submatrix_equiv_self (finSumFinEquiv.symm.trans <|
    (Equiv.ofUnique (Fin 1) m).sumCongr (Equiv.ofUnique (Fin 1) n)) A, det_fin_two]
  rfl

end Matrix

namespace Matrix

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **The alternating sum of the maximal minors of a matrix whose rows sum to one vanishes.** If
every row of a matrix `B` with `n + 2` rows and `n + 1` columns sums to `1`, then deleting the row
`p` of `B` for each `p` gives square matrices whose determinants have vanishing alternating sum. -/
theorem sum_neg_one_pow_mul_det_submatrix_succAbove_eq_zero
    (B : Matrix (Fin (n + 2)) (Fin (n + 1)) R) (hB : ∀ j, ∑ i, B j i = 1) :
    ∑ p : Fin (n + 2), (-1 : R) ^ (p : ℕ) * (B.submatrix p.succAbove id).det = 0 := by
  let A : Matrix (Fin (n + 2)) (Fin (n + 2)) R := of fun j ↦ Fin.cons 1 (B j)
  -- the first column of `A` is the sum of the others
  have hcol : A.updateCol 0 (fun k ↦ ∑ i, (Fin.cons 0 fun _ ↦ 1 : Fin (n + 2) → R) i • A k i) =
      A := by
    refine (congrArg (A.updateCol 0) (funext fun k ↦ ?_)).trans (updateCol_eq_self A 0)
    simp [A, Fin.sum_univ_succ, hB]
  have hsub (p : Fin (n + 2)) : A.submatrix p.succAbove Fin.succ = B.submatrix p.succAbove id := by
    ext j i
    simp [A]
  have hA := det_updateCol_sum A 0 (Fin.cons 0 fun _ ↦ 1)
  rw [hcol, Fin.cons_zero, zero_smul, det_succ_column_zero] at hA
  simpa [A, hsub] using hA

/-- **Expanding along a constant column `1`.** If the first column of a square matrix `N` is
constant equal to `1`, then `det N` is the determinant of the matrix of consecutive row
differences `N (i + 1) (j + 1) - N i (j + 1)` of the remaining columns.

Subtracting each row from its successor leaves `1` as the only nonzero entry of the first column,
in the first row, and the minor of that entry is the matrix of differences. -/
theorem det_eq_det_of_col_zero_eq_one (N : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hN : ∀ i, N i 0 = 1) :
    N.det = (of fun i j : Fin n => N i.succ j.succ - N i.castSucc j.succ).det := by
  rw [det_eq_of_forall_row_eq_smul_add_pred (A := N)
    (B := of (Fin.cons (N 0) fun i => N i.succ - N i.castSucc)) (fun _ => 1) (fun _ => rfl)
    (fun _ _ => by simp), det_succ_column_zero, Fin.sum_univ_succ]
  simp [hN, submatrix]

end Matrix
