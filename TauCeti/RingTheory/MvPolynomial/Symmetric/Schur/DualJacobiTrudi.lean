/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.JacobiTrudi
import TauCeti.Algebra.Ring.Parity
import TauCeti.Combinatorics.Young.BoxShuffle
import TauCeti.Combinatorics.Young.Diagram
import TauCeti.RingTheory.MvPolynomial.Symmetric.Complete.ToeplitzMinor

/-!
# The dual Jacobi--Trudi identity

The Schur polynomial `s_μ` is a determinant of elementary symmetric polynomials indexed by the
column lengths `μ'ⱼ` of `μ`:

`s_μ = det (e_{μ'ᵢ - i + j})_{0 ≤ i, j < r}`

for every `r` at least the number of columns of `μ`, in any number of variables and over any
commutative ring.  The indices are integers, and `e_m` is `0` for `m < 0`; this is
`TauCeti.esymmInt`.  Combined with the Jacobi--Trudi identity
`TauCeti.diagramSchurPoly_eq_det_hsymmInt`, it says that the determinant of complete homogeneous
symmetric polynomials attached to the rows of `μ` equals the determinant of elementary symmetric
polynomials attached to its columns, `YoungDiagram.det_hsymmInt_eq_det_esymmInt`; this form holds in
any finite alphabet.  For a one-column shape the identity is `TauCeti.schurPoly_ones`,
`s_{(1ⁿ)} = e_n`.

## The proof

The route is Macdonald's (I.2.9).  Let `μ` fit in the box with `m` rows and `n` columns, and put
`K = m + n`.

* The Toeplitz matrices `H = (h_{j - i})` and `E = ((-1)^{j - i} e_{j - i})` of size `K` are
  inverse to each other (`TauCeti.hsymmToeplitz_mul_esymmToeplitz`) and have determinant `1`.
* The `m` numbers `μ_{m-1-q} + q` and the `n` numbers `m + j - μ'ⱼ` are complementary in
  `{0, …, K - 1}` (Macdonald (I.1.7)): the first family increases in `q`, the second in `j`, and
  `m + j - μ'ⱼ < μᵢ + m - 1 - i` holds exactly when the cell `(i, j)` lies in `μ`, the reverse
  strict inequality holding otherwise.  Listing the first family and then the second is therefore
  a permutation of `{0, …, K - 1}`, `YoungDiagram.boxShufflePerm`, whose inversions are in
  bijection with the cells of `μ`, so its sign is `(-1)^{|μ|}`
  (`YoungDiagram.sign_boxShufflePerm`).
* Jacobi's complementary-minor identity for the two Toeplitz matrices,
  `TauCeti.det_submatrix_hsymmToeplitz`, applied with the shuffle `τ`, equates the minor of `H` on
  the first `m` rows and the shuffled first `m` columns with `sign τ` times the complementary minor
  of `E`.  The first is, after reversing the order of its rows and columns, the transpose of the
  Jacobi--Trudi matrix `(h_{μᵢ - i + j})`.  The second is `((-1)^{μ'ⱼ - j + k} e_{μ'ⱼ - j + k})`,
  whose determinant is `(-1)^{|μ|} det (e_{μ'ⱼ - j + k})` by
  `TauCeti.det_submatrix_esymmToeplitz`, and the signs cancel.

## Main results

* `YoungDiagram.det_hsymmInt_eq_det_esymmInt`: for `μ` inside the `m × n` box,
  `det (h_{μᵢ - i + j})_{i, j < m} = det (e_{μ'ᵢ - i + j})_{i, j < n}`.
* `TauCeti.diagramSchurPoly_eq_det_esymmInt`: **the dual Jacobi--Trudi identity** for the Schur
  polynomial of a Young diagram.
* `Nat.Partition.schurPoly_eq_det_esymmInt`: the dual Jacobi--Trudi identity for the Schur
  polynomial of a partition.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  (1.7), (2.9), (3.5).
* R. P. Stanley, *Enumerative Combinatorics, Vol. 2*, Corollary 7.16.2.
-/

public section

/-! ### The dual Jacobi--Trudi identity -/

namespace YoungDiagram

open TauCeti MvPolynomial Finset

variable {R : Type*} [CommRing R] {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- **The `h`-determinant of the rows equals the `e`-determinant of the columns.**  For a Young
diagram `μ` with at most `m` rows and at most `n` columns,
`det (h_{μᵢ - i + j})_{i, j < m} = det (e_{μ'ᵢ - i + j})_{i, j < n}`, where `μᵢ` and `μ'ᵢ` are the
row and column lengths, and `h_k = e_k = 0` for `k < 0`.  By the Jacobi--Trudi identity the left
side is the Schur polynomial `s_μ`, so this is the dual Jacobi--Trudi identity in determinant
form. -/
theorem det_hsymmInt_eq_det_esymmInt (μ : YoungDiagram) {m n : ℕ} (hm : μ.colLen 0 ≤ m)
    (hn : μ.rowLen 0 ≤ n) :
    (Matrix.of fun i j : Fin m => hsymmInt σ R ((μ.rowLen i : ℤ) - (i : ℕ) + (j : ℕ))).det =
      (Matrix.of fun i j : Fin n => esymmInt σ R ((μ.colLen i : ℤ) - (i : ℕ) + (j : ℕ))).det := by
  set τ := boxShufflePerm hm hn
  have hcol : ∀ j, μ.colLen j ≤ m := fun j ↦ (μ.colLen_anti 0 j j.zero_le).trans hm
  -- Split `Fin (m + n)` as `Fin n ⊕ Fin m`, so that the `Fin m` part is the first `m` indices.
  set e := (Equiv.sumComm (Fin n) (Fin m)).trans finSumFinEquiv
  -- The minor of `H` on the first `m` rows and the shuffled first `m` columns is the
  -- Jacobi--Trudi matrix, reversed and transposed.
  have hH : (hsymmToeplitz σ R (m + n)).submatrix (⇑(1 : Equiv.Perm (Fin (m + n))) ∘ ⇑e ∘ Sum.inr)
      (⇑τ ∘ ⇑e ∘ Sum.inr) = ((Matrix.of fun i j : Fin m =>
        hsymmInt σ R ((μ.rowLen i : ℤ) - (i : ℕ) + (j : ℕ))).submatrix Fin.revPerm
          Fin.revPerm).transpose := by
    refine Matrix.ext fun p q ↦ ?_
    simp only [e, Matrix.of_apply, Matrix.submatrix_apply, Matrix.transpose_apply,
      Function.comp_apply, Equiv.trans_apply, Equiv.sumComm_apply, Sum.swap_inr,
      finSumFinEquiv_apply_left, Equiv.Perm.coe_one, id_eq, hsymmToeplitz_apply,
      boxShufflePerm_apply_val, τ, Fin.val_castAdd, boxShuffle_def, q.isLt, ↓reduceIte,
      Fin.revPerm_apply, Fin.val_rev]
    congr 1
    omega
  -- The complementary minor of `E`, stripped of its signs, is the dual Jacobi--Trudi matrix.
  have hrow : ∀ j : Fin n, (((τ ∘ e ∘ Sum.inl) j : Fin (m + n)) : ℕ) = m + j - μ.colLen j := by
    intro j
    simp only [e, Function.comp_apply, Equiv.trans_apply, Equiv.sumComm_apply, Sum.swap_inl,
      finSumFinEquiv_apply_right, boxShufflePerm_apply_val, τ, Fin.val_natAdd, boxShuffle_def,
      show ¬(m + (j : ℕ) < m) by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  have hcolIdx : ∀ k : Fin n, (((e ∘ Sum.inl) k : Fin (m + n)) : ℕ) = m + k := by
    intro k
    simp [e]
  have hE : (Matrix.of fun j k : Fin n =>
      esymmInt σ R ((((e ∘ Sum.inl) k : Fin (m + n)) : ℤ) - ((τ ∘ e ∘ Sum.inl) j : ℕ))) =
      Matrix.of fun i j : Fin n => esymmInt σ R ((μ.colLen i : ℤ) - (i : ℕ) + (j : ℕ)) := by
    refine Matrix.ext fun j k ↦ ?_
    simp only [Matrix.of_apply]
    rw [hrow, hcolIdx]
    congr 1
    have := hcol j
    omega
  -- The row signs `(-1)^{m + j - μ'ⱼ}` and the column signs `(-1)^{m + j}` leave `(-1)^{∑ μ'ⱼ}`.
  have hcard : ∑ j : Fin n, μ.colLen j = μ.card := by
    rw [Fin.sum_univ_eq_sum_range (fun j ↦ μ.colLen j), ← μ.card_transpose,
      YoungDiagram.card_eq_sum_range_rowLen μ.transpose (N := n)
        (by rw [YoungDiagram.colLen_transpose]; exact hn)]
    simp only [YoungDiagram.rowLen_transpose]
  have hsigns : (∏ j : Fin n, (-1 : MvPolynomial σ R) ^ (((τ ∘ e ∘ Sum.inl) j : Fin _) : ℕ)) *
      ∏ k : Fin n, (-1 : MvPolynomial σ R) ^ (((e ∘ Sum.inl) k : Fin _) : ℕ) =
      (-1) ^ μ.card := by
    rw [← hcard, ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
    refine prod_congr rfl fun j _ ↦ ?_
    rw [hrow, hcolIdx, ← pow_add,
      show m + j - μ.colLen j + (m + j) = μ.colLen j + 2 * (m + j - μ.colLen j) by
        have := hcol j
        omega,
      neg_one_pow_add_two_mul]
  -- Jacobi's complementary-minor identity for the two Toeplitz matrices relates the two minors.
  have key := det_submatrix_hsymmToeplitz σ R (m + n) e τ 1
  rw [hH, det_submatrix_esymmToeplitz, Equiv.Perm.coe_one, Function.id_comp, hE,
    Matrix.det_transpose, Matrix.det_submatrix_equiv_self, sign_boxShufflePerm,
    Equiv.Perm.sign_one] at key
  rw [key, mul_right_comm _ (Matrix.det _), hsigns]
  push_cast
  simp

end YoungDiagram

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- **The dual Jacobi--Trudi identity.**  The Schur polynomial of a Young diagram `μ` in the
alphabet `Fin N` is the determinant `det (e_{μ'ᵢ - i + j})_{0 ≤ i, j < r}` of elementary symmetric
polynomials, where `μ'ᵢ` is the length of the `i`-th column, for every `r` at least the number of
columns of `μ`.  The index `μ'ᵢ - i + j` is an integer, and `e_m = 0` for `m < 0`
(`TauCeti.esymmInt`). -/
theorem diagramSchurPoly_eq_det_esymmInt (N : ℕ) (μ : YoungDiagram) {r : ℕ}
    (hr : μ.rowLen 0 ≤ r) :
    diagramSchurPoly N R μ =
      (Matrix.of fun i j : Fin r =>
        esymmInt (Fin N) R ((μ.colLen i : ℤ) - (i : ℕ) + (j : ℕ))).det := by
  rw [diagramSchurPoly_eq_det_hsymmInt N μ le_rfl, μ.det_hsymmInt_eq_det_esymmInt le_rfl hr]

end TauCeti

namespace Nat.Partition

open TauCeti

variable {R : Type*} [CommRing R] {σ : Type*} [Fintype σ]

/-- **The dual Jacobi--Trudi identity for partitions.**  In a finite alphabet `σ`, the Schur
polynomial of a partition `μ` is `det (e_{μ'ᵢ - i + j})_{0 ≤ i, j < r}`, where `μ'ᵢ` is the length
of the `i`-th column of the Young diagram of `μ`, for every `r` at least the largest part of `μ`,
and `e_m = 0` for `m < 0`. -/
theorem schurPoly_eq_det_esymmInt {n : ℕ} (μ : n.Partition) {r : ℕ}
    (hr : (YoungDiagram.ofPartition μ).rowLen 0 ≤ r) :
    schurPoly σ R μ =
      (Matrix.of fun i j : Fin r =>
        esymmInt σ R (((YoungDiagram.ofPartition μ).colLen i : ℤ) - (i : ℕ) + (j : ℕ))).det := by
  classical
  rw [schurPoly_eq_det_hsymmInt μ le_rfl,
    YoungDiagram.det_hsymmInt_eq_det_esymmInt _ (YoungDiagram.colLen_zero_ofPartition μ).le hr]

end Nat.Partition
