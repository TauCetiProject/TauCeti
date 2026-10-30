/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.JacobiTrudi
import TauCeti.Combinatorics.Young.Diagram
import TauCeti.GroupTheory.Perm.Inversion
import TauCeti.LinearAlgebra.Matrix.Determinant.ComplementaryMinor
import TauCeti.RingTheory.MvPolynomial.Symmetric.Complete.Elementary

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
polynomials attached to its columns, `TauCeti.det_hsymmInt_eq_det_esymmInt`; this form holds in
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
  a permutation of `{0, …, K - 1}` whose inversions are in bijection with the cells of `μ`, so
  its sign is `(-1)^{|μ|}`.
* Permuting the columns of `H` and the rows of `E` by this shuffle keeps them mutually inverse.
  The top-left `m × m` block of the permuted `H` is, after reversing the order of its rows and
  columns, the transpose of the Jacobi--Trudi matrix `(h_{μᵢ - i + j})`, and the bottom-right
  `n × n` block of the permuted `E` is `((-1)^{μ'ⱼ - j + k} e_{μ'ⱼ - j + k})`, whose determinant
  is `(-1)^{|μ|} det (e_{μ'ⱼ - j + k})`.  Jacobi's complementary-minor identity
  `Matrix.det_mul_det_toBlocks₂₂_of_mul_eq_one` relates the two blocks, and the signs cancel.

## Main results

* `TauCeti.det_hsymmInt_eq_det_esymmInt`: for `μ` inside the `m × n` box,
  `det (h_{μᵢ - i + j})_{i, j < m} = det (e_{μ'ᵢ - i + j})_{i, j < n}`.
* `TauCeti.diagramSchurPoly_eq_det_esymmInt`: **the dual Jacobi--Trudi identity** for the Schur
  polynomial of a Young diagram.
* `TauCeti.schurPoly_eq_det_esymmInt`: the dual Jacobi--Trudi identity for the Schur polynomial
  of a partition.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  (1.7), (2.9), (3.5).
* R. P. Stanley, *Enumerative Combinatorics, Vol. 2*, Corollary 7.16.2.
-/

public section

namespace TauCeti

open MvPolynomial Finset

variable {R : Type*} [CommRing R]

/-! ### The shuffle of the rows and columns of a diagram in a box -/

section Shuffle

variable (μ : YoungDiagram) (m : ℕ)

/-- The shuffle attached to a diagram `μ` with at most `m` rows: an index `k < m` goes to
`μ_{m-1-k} + k`, and an index `m + j` goes to `m + j - μ'ⱼ`. -/
private def shuffle (k : ℕ) : ℕ :=
  if k < m then μ.rowLen (m - (k + 1)) + k else k - μ.colLen (k - m)

/-- An index `k < m` and an index `k' ≥ m` whose cell `(m - 1 - k, k' - m)` lies in the diagram
are an inversion of the shuffle. -/
private theorem shuffle_lt_shuffle_of_mem {k k' : ℕ} (hk : k < m) (hk' : m ≤ k')
    (hmem : (m - (k + 1), k' - m) ∈ μ) : shuffle μ m k' < shuffle μ m k := by
  have hrow := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have hcol := YoungDiagram.mem_iff_lt_colLen.mp hmem
  simp only [shuffle, hk, show ¬k' < m by omega, ↓reduceIte]
  omega

/-- Every other pair of indices `k < k'` is ordered by the shuffle: within the first `m` indices
and within the rest the shuffle increases, and across them it increases unless the corresponding
cell lies in the diagram. -/
private theorem shuffle_lt_shuffle_of_not {k k' : ℕ} (hm : μ.colLen 0 ≤ m) (hkk' : k < k')
    (h : ¬(k < m ∧ m ≤ k' ∧ (m - (k + 1), k' - m) ∈ μ)) : shuffle μ m k < shuffle μ m k' := by
  have hcol : ∀ j, μ.colLen j ≤ m := fun j ↦ (μ.colLen_anti 0 j j.zero_le).trans hm
  by_cases hk' : k' < m
  · have := μ.rowLen_anti (m - (k' + 1)) (m - (k + 1)) (by omega)
    simp only [shuffle, hk', hkk'.trans hk', ↓reduceIte]
    omega
  by_cases hk : k < m
  · have hmem : (m - (k + 1), k' - m) ∉ μ := fun hmem ↦ h ⟨hk, by omega, hmem⟩
    have hrow := mt YoungDiagram.mem_iff_lt_rowLen.mpr hmem
    have hcol' := mt YoungDiagram.mem_iff_lt_colLen.mpr hmem
    have := hcol (k' - m)
    simp only [shuffle, hk, hk', ↓reduceIte]
    omega
  · have := μ.colLen_anti (k - m) (k' - m) (by omega)
    have := hcol (k - m)
    simp only [shuffle, hk, hk', ↓reduceIte]
    omega

/-- **The inversions of the shuffle are the cells of the diagram** (Macdonald (I.1.7)). -/
private theorem shuffle_lt_shuffle_iff {k k' : ℕ} (hm : μ.colLen 0 ≤ m) (hkk' : k < k') :
    shuffle μ m k' < shuffle μ m k ↔ k < m ∧ m ≤ k' ∧ (m - (k + 1), k' - m) ∈ μ :=
  ⟨fun hlt ↦ by_contra fun h ↦ (shuffle_lt_shuffle_of_not μ m hm hkk' h).not_gt hlt,
    fun ⟨hk, hk', hmem⟩ ↦ shuffle_lt_shuffle_of_mem μ m hk hk' hmem⟩

private theorem shuffle_injective (hm : μ.colLen 0 ≤ m) {k k' : ℕ} (hkk' : k < k') :
    shuffle μ m k' ≠ shuffle μ m k := by
  by_cases h : k < m ∧ m ≤ k' ∧ (m - (k + 1), k' - m) ∈ μ
  · exact (shuffle_lt_shuffle_of_mem μ m h.1 h.2.1 h.2.2).ne
  · exact (shuffle_lt_shuffle_of_not μ m hm hkk' h).ne'

private theorem shuffle_lt {n k : ℕ} (hn : μ.rowLen 0 ≤ n) (hk : k < m + n) :
    shuffle μ m k < m + n := by
  have := μ.rowLen_anti 0 (m - (k + 1)) (Nat.zero_le _)
  unfold shuffle
  split_ifs <;> omega

variable {μ m} {n : ℕ}

/-- The shuffle of a diagram in the box with `m` rows and `n` columns, as a permutation of
`Fin (m + n)`. -/
private noncomputable def shufflePerm (hm : μ.colLen 0 ≤ m) (hn : μ.rowLen 0 ≤ n) :
    Equiv.Perm (Fin (m + n)) :=
  Equiv.ofBijective (fun k ↦ ⟨shuffle μ m k, shuffle_lt μ m hn k.isLt⟩) <|
    Finite.injective_iff_bijective.mp fun a b hab ↦ by
      by_contra hne
      have hab' : shuffle μ m a = shuffle μ m b := congrArg Fin.val hab
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
      · exact shuffle_injective μ m hm h hab'.symm
      · exact shuffle_injective μ m hm h hab'

private theorem shufflePerm_apply_val (hm : μ.colLen 0 ≤ m) (hn : μ.rowLen 0 ≤ n)
    (k : Fin (m + n)) : (shufflePerm hm hn k : ℕ) = shuffle μ m k :=
  rfl

/-- The shuffle has one inversion for each cell of the diagram. -/
private theorem card_inversions_shufflePerm (hm : μ.colLen 0 ≤ m) (hn : μ.rowLen 0 ≤ n) :
    #(univ.inversions (shufflePerm hm hn)) = μ.card := by
  refine card_nbij (fun p ↦ (m - ((p.1 : ℕ) + 1), (p.2 : ℕ) - m)) ?_ ?_ ?_
  · rintro ⟨x, y⟩ hp
    simp only [mem_coe, mem_inversions, mem_univ, true_and, Fin.lt_def,
      shufflePerm_apply_val] at hp
    exact (YoungDiagram.mem_cells _).mpr ((shuffle_lt_shuffle_iff μ m hm hp.1).mp hp.2).2.2
  · rintro ⟨x, y⟩ hp ⟨x', y'⟩ hp' hxy
    simp only [mem_coe, mem_inversions, mem_univ, true_and, Fin.lt_def,
      shufflePerm_apply_val] at hp hp'
    have h := (shuffle_lt_shuffle_iff μ m hm hp.1).mp hp.2
    have h' := (shuffle_lt_shuffle_iff μ m hm hp'.1).mp hp'.2
    simp only [Prod.mk.injEq] at hxy
    rw [Prod.mk.injEq, Fin.ext_iff, Fin.ext_iff]
    omega
  · rintro ⟨i, j⟩ hc
    have hc' : (i, j) ∈ μ := (YoungDiagram.mem_cells _).mp hc
    have hi : i < m := (YoungDiagram.lt_colLen_zero_of_mem hc').trans_le hm
    have hj : j < n := (YoungDiagram.mem_iff_lt_rowLen.mp hc').trans_le
      ((μ.rowLen_anti 0 i i.zero_le).trans hn)
    refine ⟨(⟨m - (i + 1), by omega⟩, ⟨m + j, by omega⟩), ?_, ?_⟩
    · simp only [mem_coe, mem_inversions, mem_univ, true_and, Fin.lt_def, shufflePerm_apply_val]
      refine ⟨by omega, (shuffle_lt_shuffle_iff μ m hm (by omega)).mpr ⟨by omega, by omega, ?_⟩⟩
      simpa only [show m - (m - (i + 1) + 1) = i by omega, Nat.add_sub_cancel_left] using hc'
    · simp only [Prod.mk.injEq]
      omega

/-- The sign of the shuffle is `(-1)` to the number of cells of the diagram. -/
private theorem sign_shufflePerm (hm : μ.colLen 0 ≤ m) (hn : μ.rowLen 0 ≤ n) :
    Equiv.Perm.sign (shufflePerm hm hn) = (-1) ^ μ.card := by
  rw [sign_eq_neg_one_pow_card_inversion, card_inversions_shufflePerm]

end Shuffle

/-! ### The dual Jacobi--Trudi identity -/

section DualJacobiTrudi

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [DecidableEq σ] in
/-- The sign `(-1)^{c - j + k}` of the entry `e_{c - j + k}` of a signed Toeplitz matrix splits
as a row sign `(-1)^{c + j}` and a column sign `(-1)^k`; when `c - j + k < 0` the entry vanishes,
whatever its sign. -/
private theorem neg_one_pow_toNat_mul_esymmInt (c j k : ℕ) :
    (-1 : MvPolynomial σ R) ^ ((c : ℤ) - j + k).toNat * esymmInt σ R ((c : ℤ) - j + k) =
      (-1) ^ (c + j) * ((-1) ^ k * esymmInt σ R ((c : ℤ) - j + k)) := by
  rcases lt_or_ge ((c : ℤ) - j + k) 0 with h | h
  · simp [esymmInt_of_neg h]
  · rw [← mul_assoc, ← pow_add, show c + j + k = ((c : ℤ) - j + k).toNat + 2 * j by omega,
      pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

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
  set τ := shufflePerm hm hn
  have hcol : ∀ j, μ.colLen j ≤ m := fun j ↦ (μ.colLen_anti 0 j j.zero_le).trans hm
  -- Permute the columns of `H` and the rows of `E` by the shuffle; they stay mutually inverse.
  set M := (hsymmToeplitz σ R (m + n)).submatrix finSumFinEquiv (finSumFinEquiv.trans τ)
  set N := (esymmToeplitz σ R (m + n)).submatrix (finSumFinEquiv.trans τ) finSumFinEquiv
  have hMN : M * N = 1 := by
    rw [Matrix.submatrix_mul_equiv, hsymmToeplitz_mul_esymmToeplitz, Matrix.submatrix_one_equiv]
  have hM : M.det = (-1) ^ μ.card := by
    have : M = ((hsymmToeplitz σ R (m + n)).submatrix id τ).submatrix finSumFinEquiv
        finSumFinEquiv := by
      simp only [M, Matrix.submatrix_submatrix, Equiv.coe_trans, Function.id_comp]
    rw [this, Matrix.det_submatrix_equiv_self, Matrix.det_permute', det_hsymmToeplitz, mul_one,
      sign_shufflePerm]
    simp
  -- The top-left block of `M` is the Jacobi--Trudi matrix, reversed and transposed.
  have h₁₁ : M.toBlocks₁₁ = ((Matrix.of fun i j : Fin m =>
      hsymmInt σ R ((μ.rowLen i : ℤ) - (i : ℕ) + (j : ℕ))).submatrix Fin.revPerm
        Fin.revPerm).transpose := by
    refine Matrix.ext fun p q ↦ ?_
    simp only [Matrix.toBlocks₁₁, M, Matrix.of_apply, Matrix.submatrix_apply,
      Matrix.transpose_apply, Equiv.trans_apply, finSumFinEquiv_apply_left, hsymmToeplitz_apply,
      shufflePerm_apply_val, τ, Fin.val_castAdd, shuffle, q.isLt, ↓reduceIte, Fin.revPerm_apply,
      Fin.val_rev]
    congr 1
    omega
  -- The bottom-right block of `N` is the dual Jacobi--Trudi matrix with signs `(-1)^{μ'ⱼ - j + k}`.
  set E' := Matrix.of fun i j : Fin n => esymmInt σ R ((μ.colLen i : ℤ) - (i : ℕ) + (j : ℕ))
  have h₂₂ : N.toBlocks₂₂ = Matrix.of fun j k : Fin n => (-1) ^ (μ.colLen j + (j : ℕ)) *
      (Matrix.of fun j k : Fin n => (-1) ^ (k : ℕ) * E' j k) j k := by
    refine Matrix.ext fun j k ↦ ?_
    have hidx : ((m + k : ℕ) : ℤ) - ((m + j - μ.colLen j : ℕ) : ℤ) =
        (μ.colLen j : ℤ) - (j : ℕ) + (k : ℕ) := by
      have := hcol j
      omega
    simp only [Matrix.toBlocks₂₂, N, E', Matrix.of_apply, Matrix.submatrix_apply, Equiv.trans_apply,
      finSumFinEquiv_apply_right, esymmToeplitz_apply, shufflePerm_apply_val, τ, Fin.val_natAdd,
      shuffle, show ¬(m + (j : ℕ) < m) by omega, ↓reduceIte, Nat.add_sub_cancel_left]
    rw [hidx, neg_one_pow_toNat_mul_esymmInt]
  have hN : N.toBlocks₂₂.det = (-1) ^ μ.card * E'.det := by
    rw [h₂₂, Matrix.det_mul_column, Matrix.det_mul_row, ← mul_assoc]
    congr 1
    -- The row signs `(-1)^j` and the column signs `(-1)^k` cancel, leaving `(-1)^{∑ μ'ⱼ}`.
    have hcard : ∑ j : Fin n, μ.colLen j = μ.card := by
      rw [Fin.sum_univ_eq_sum_range (fun j ↦ μ.colLen j), ← μ.card_transpose,
        YoungDiagram.card_eq_sum_range_rowLen μ.transpose (N := n)
          (by rw [YoungDiagram.colLen_transpose]; exact hn)]
      simp only [YoungDiagram.rowLen_transpose]
    rw [← hcard, ← prod_pow_eq_pow_sum, ← prod_mul_distrib]
    refine prod_congr rfl fun j _ ↦ ?_
    rw [pow_add, mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, mul_one]
  have key := Matrix.det_mul_det_toBlocks₂₂_of_mul_eq_one hMN
  rw [hM, hN, h₁₁, Matrix.det_transpose, Matrix.det_submatrix_equiv_self, ← mul_assoc, ← pow_add,
    ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul] at key
  exact key.symm

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
  rw [diagramSchurPoly_eq_det_hsymmInt N μ le_rfl, det_hsymmInt_eq_det_esymmInt μ le_rfl hr]

omit [DecidableEq σ] in
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
    det_hsymmInt_eq_det_esymmInt _ (YoungDiagram.colLen_zero_ofPartition μ).le hr]

end DualJacobiTrudi

end TauCeti
