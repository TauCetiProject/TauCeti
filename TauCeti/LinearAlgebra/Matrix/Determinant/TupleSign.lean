/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Signs of tuples

Given an ordering `e : κ ≃ ι` of a finite type `κ`, the sign `e.tupleSign R a` of a tuple
`a : ι → κ` is the determinant of the matrix whose row `j` is the standard basis vector indexed by
`e (a j)`. It is the sign of the permutation `e ∘ a` when `a` is bijective, and `0` otherwise.

For `ι = Fin (n + 1)`, the signs of the tuples obtained by deleting one entry of a tuple of length
`n + 2` have vanishing alternating sum: the signs of tuples form a Čech cocycle. This is an
instance of `Matrix.sum_neg_one_pow_mul_det_submatrix_succAbove_eq_zero`, about matrices with
`n + 2` rows and `n + 1` columns every row of which sums to `1`.

## Main results

* `Equiv.tupleSign_comp_perm`, `Equiv.tupleSign_eq_zero_of_not_surjective`: the sign of a tuple is
  alternating, and vanishes on tuples which are not surjective.
* `Equiv.sum_neg_one_pow_mul_tupleSign_comp_succAbove`: the signs of tuples form a Čech cocycle.
-/

public section

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
