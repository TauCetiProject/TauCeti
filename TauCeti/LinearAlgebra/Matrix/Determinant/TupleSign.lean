/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Signs of tuples

Given an ordering `e : κ ≃ ι` of a finite type `κ`, the sign `e.tupleSign R a` of a tuple
`a : ι → κ` is the determinant of the matrix whose row `j` is the standard basis vector indexed by
`e (a j)`. It is the sign of the permutation `e ∘ a` when `a` is bijective, and `0` otherwise.

For `ι = Fin (n + 1)`, the signs of the tuples obtained by deleting one entry of a tuple of length
`n + 2` have vanishing alternating sum: the signs of tuples form a Čech cocycle. This is an
instance of a fact about any matrix `B` with `n + 2` rows and `n + 1` columns, every row of which
sums to `1`: deleting the rows of `B` one at a time gives `n + 2` square matrices, and the
alternating sum of their determinants vanishes. Indeed, it is the expansion along the first column
of the square matrix obtained from `B` by adjoining a first column of ones, and that column is the
sum of the others.

## Main results

* `Matrix.sum_neg_one_pow_mul_det_submatrix_succAbove_eq_zero`: the alternating sum of the maximal
  minors of a matrix with `n + 2` rows and `n + 1` columns whose rows sum to `1` vanishes.
* `Equiv.tupleSign_comp_perm`, `Equiv.tupleSign_eq_zero_of_not_surjective`: the sign of a tuple is
  alternating, and vanishes on tuples which are not surjective.
* `Equiv.sum_neg_one_pow_mul_tupleSign_comp_succAbove`: the signs of tuples form a Čech cocycle.
-/

public section

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

end Matrix

namespace Equiv

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] (R : Type*) [CommRing R]

/-- The sign of a tuple `a : ι → κ` relative to an ordering `e : κ ≃ ι` of `κ`: the determinant of
the matrix whose row `j` is the standard basis vector indexed by `e (a j)`. It is the sign of the
permutation `e ∘ a` when `a` is bijective (`Equiv.tupleSign_comp_perm`), and `0` otherwise
(`Equiv.tupleSign_eq_zero_of_not_surjective`). -/
def tupleSign (e : κ ≃ ι) (a : ι → κ) : R :=
  ((1 : Matrix ι ι R).submatrix (e ∘ a) id).det

/-- The ordering `e.symm` itself has sign `1`. -/
@[simp]
theorem tupleSign_symm (e : κ ≃ ι) : e.tupleSign R e.symm = 1 := by
  simp [tupleSign]

/-- A tuple which is not surjective has sign `0`: the matrix of the tuple has a zero column. -/
theorem tupleSign_eq_zero_of_not_surjective (e : κ ≃ ι) {a : ι → κ}
    (ha : ¬Function.Surjective a) : e.tupleSign R a = 0 := by
  obtain ⟨x, hx⟩ := not_forall.1 ha
  refine Matrix.det_eq_zero_of_column_eq_zero (e x) fun j ↦ ?_
  simp only [Matrix.submatrix_apply, Function.comp_apply, id_eq, Matrix.one_apply,
    EmbeddingLike.apply_eq_iff_eq, ite_eq_right_iff]
  exact fun h ↦ absurd ⟨j, h⟩ hx

/-- The sign of a tuple is alternating: permuting its entries by `σ` multiplies it by the sign
of `σ`. -/
theorem tupleSign_comp_perm (e : κ ≃ ι) (a : ι → κ) (σ : Perm ι) :
    e.tupleSign R (a ∘ σ) = Perm.sign σ * e.tupleSign R a :=
  Matrix.det_permute σ ((1 : Matrix ι ι R).submatrix (e ∘ a) id)

/-- **The signs of tuples form a Čech cocycle.** Deleting the entries of a tuple of `n + 2`
elements of `κ` one at a time gives tuples whose signs relative to an ordering
`e : κ ≃ Fin (n + 1)` have vanishing alternating sum. -/
theorem sum_neg_one_pow_mul_tupleSign_comp_succAbove {n : ℕ} (e : κ ≃ Fin (n + 1))
    (k : Fin (n + 2) → κ) :
    ∑ p : Fin (n + 2), (-1 : R) ^ (p : ℕ) * e.tupleSign R (k ∘ p.succAbove) = 0 :=
  Matrix.sum_neg_one_pow_mul_det_submatrix_succAbove_eq_zero
    ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R).submatrix (e ∘ k) id) fun j ↦ by
      simp [Matrix.one_apply]

end Equiv
