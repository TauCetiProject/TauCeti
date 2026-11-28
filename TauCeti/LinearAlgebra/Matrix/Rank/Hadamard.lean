/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import TauCeti.LinearAlgebra.Matrix.Rank
import TauCeti.Algebra.BigOperators.Finset.Pairs

/-!
# Ranks of entrywise products

Over a field, the rank of the entrywise (Hadamard) product `A ⊙ B` is at most `rk A · rk B`,
and the rank of the entrywise square `A ⊙ A` is at most `rk A (rk A + 1) / 2`. These bounds
are the linear-algebraic input of the absolute bound for association schemes, from the proof of
Theorem 2.3.3 of Brouwer, Cohen and Neumaier. The bounds are stated for finitely many columns.
Without any finiteness they fail: the identity matrix on `ℕ` has the junk rank `0`, but its
entrywise product with a matrix of rank one has rank one.

The proof factors `A = L * R` and `B = L' * R'` through `Fin (rk A)` and `Fin (rk B)`. The
entrywise product of two products is again a product, through the product of the two inner
index types (`Matrix.mul_hadamard_mul`). For `A ⊙ A` the inner sum is symmetric in the two
indices, so the diagonal pairs `(a, a)` and the pairs `(a, b)` with `a < b` suffice
(`TauCeti.sum_symmetric_pairs`); there are `(rk A + 1).choose 2` of them.

## Main results

* `Matrix.mul_hadamard_mul`: `(L * R) ⊙ (L' * R')` factors through the product of the inner
  index types.
* `Matrix.rank_hadamard_le`: `rk (A ⊙ B) ≤ rk A · rk B`.
* `Matrix.two_mul_rank_hadamard_self_le`: `2 rk (A ⊙ A) ≤ rk A (rk A + 1)`.

## References

* A. E. Brouwer, A. M. Cohen, A. Neumaier, *Distance-Regular Graphs*, Ergebnisse der Mathematik
  und ihrer Grenzgebiete (3) 18, Springer, 1989, Theorem 2.3.3, p. 51.
-/

public section

namespace Matrix

section Semiring

variable {m n ι κ α : Type*} [Fintype ι] [Fintype κ] [NonUnitalCommSemiring α]

/-- The entrywise product of two matrix products is a matrix product through the product of
the two inner index types: the left factor has the entrywise products of the columns of `L`
and `L'`, and the right factor has the entrywise products of the rows of `R` and `R'`. -/
theorem mul_hadamard_mul (L : Matrix m ι α) (R : Matrix ι n α) (L' : Matrix m κ α)
    (R' : Matrix κ n α) :
    (L * R) ⊙ (L' * R') =
      (of fun i (p : ι × κ) => L i p.1 * L' i p.2 : Matrix m (ι × κ) α) *
        (of fun (p : ι × κ) j => R p.1 j * R' p.2 j : Matrix (ι × κ) n α) := by
  ext i j
  simp only [hadamard_apply, Matrix.mul_apply, of_apply, Fintype.sum_prod_type,
    Fintype.sum_mul_sum, mul_mul_mul_comm]

end Semiring

section Field

variable {m n K : Type*} [Finite n] [Field K]

/-- **The rank of an entrywise product.** Over a field, for matrices with finitely many columns,
`rk (A ⊙ B) ≤ rk A · rk B`. -/
theorem rank_hadamard_le (A B : Matrix m n K) : (A ⊙ B).rank ≤ A.rank * B.rank := by
  obtain ⟨L, R, hA⟩ := A.exists_eq_mul_fin_rank
  obtain ⟨L', R', hB⟩ := B.exists_eq_mul_fin_rank
  have h := mul_hadamard_mul L R L' R'
  rw [← hA, ← hB] at h
  rw [h]
  refine (rank_mul_le_left _ _).trans ((rank_le_card_width _).trans ?_)
  simp

/-- **The rank of an entrywise square.** Over a field, for a matrix with finitely many columns,
`2 rk (A ⊙ A) ≤ rk A (rk A + 1)`: the rows of `A ⊙ A` are combinations of the
`rk A (rk A + 1) / 2` entrywise products `u_a ⊙ u_b` with `a ≤ b` of `rk A` rows `u_a` that
span the rows of `A`. -/
theorem two_mul_rank_hadamard_self_le (A : Matrix m n K) :
    2 * (A ⊙ A).rank ≤ A.rank * (A.rank + 1) := by
  obtain ⟨L, R, hA⟩ := A.exists_eq_mul_fin_rank
  let S := Fin A.rank ⊕ {p : Fin A.rank × Fin A.rank // p.1 < p.2}
  have h : A ⊙ A =
      (of fun i => Sum.elim (fun a => L i a * L i a)
        (fun p => 2 * (L i p.val.1 * L i p.val.2)) : Matrix m S K) *
      (of fun s j => Sum.elim (fun a => R a j * R a j) (fun p => R p.val.1 j * R p.val.2 j) s :
        Matrix S n K) := by
    conv_lhs => rw [hA, mul_hadamard_mul]
    ext i j
    simp only [Matrix.mul_apply, of_apply, Fintype.sum_prod_type]
    rw [TauCeti.sum_symmetric_pairs (fun a b => L i a * L i b * (R a j * R b j))
      fun a b => by ring, Fintype.sum_sum_type]
    simp [nsmul_eq_mul, Finset.mul_sum, mul_assoc]
  have hcard : Fintype.card S = (A.rank + 1).choose 2 := by
    rw [Fintype.card_sum, Fintype.card_subtype, Fintype.card_product_filter_lt, Fintype.card_fin,
      Nat.choose_succ_succ, Nat.choose_one_right]
  calc 2 * (A ⊙ A).rank ≤ 2 * (A.rank + 1).choose 2 := by
        rw [h, ← hcard]
        exact Nat.mul_le_mul_left _ ((rank_mul_le_left _ _).trans (rank_le_card_width _))
    _ = A.rank * (A.rank + 1) := by
        rw [Nat.choose_two_right, Nat.add_sub_cancel, mul_comm (A.rank + 1),
          Nat.mul_div_cancel' (Nat.even_mul_succ_self A.rank).two_dvd]

end Field

end Matrix
