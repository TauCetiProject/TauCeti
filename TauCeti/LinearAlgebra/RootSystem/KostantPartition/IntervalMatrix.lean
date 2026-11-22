/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Determinant.TotallyUnimodular

/-!
# The type-A interval matrix

The positive roots of type `A_{N-1}` are `e_i - e_j` for `0 ≤ i < j < N`, indexed by
`TauCeti.PositiveInterval N`. In the coordinates of the simple roots `α_k = e_k - e_{k+1}`,
`0 ≤ k < N - 1`, the root `e_i - e_j = α_i + ⋯ + α_{j-1}` has coefficient `1` at the positions
`i ≤ k < j` and `0` elsewhere. Collecting these coefficient vectors as columns gives the
**interval matrix** `TauCeti.intervalMatrix N`, an `(N - 1) × N(N - 1)/2` integer matrix every
column of which is the indicator of an interval of rows. Writing a vector `b` of simple-root
coordinates as a nonnegative integer combination of its columns is the same as writing
`∑ₖ bₖ αₖ` as a sum of positive roots, so the type-A Kostant partition function counts the
nonnegative integer solutions of `intervalMatrix N *ᵥ c = b`.

The three facts below are the hypotheses under which such vector partition counts are
piecewise polynomial in `b`:

* `TauCeti.intervalMatrix_isTotallyUnimodular`: every square minor is `0`, `1` or `-1`, the
  type-A instance of the total unimodularity of interval matrices
  (`Matrix.isTotallyUnimodular_of_col_eq_indicator_ordConnected`);
* `TauCeti.intervalMatrix_submatrix_simpleInterval`: the columns of the simple roots form the
  identity matrix, so the matrix has full row rank and its columns span `ℤ^{N-1}`;
* `TauCeti.sum_intervalMatrix_apply`: the all-ones covector takes the value `j - i`, the height
  of the root `e_i - e_j`, on the column `(i, j)`; it is positive on every column
  (`TauCeti.sum_intervalMatrix_apply_pos`).

## References

* S. Billey, V. Guillemin and E. Rassart, *A vector partition function for the multiplicities
  of `sl_k ℂ`*, J. Algebra **278** (2004), 251–293, §1.3 and Lemma 1.6.
-/

public section

open Matrix

namespace TauCeti

/-- The index type of the positive roots `e_i - e_j` of type `A_{N-1}`: pairs `(i, j)` of
elements of `Fin N` with `i < j`. -/
abbrev PositiveInterval (N : ℕ) : Type := {p : Fin N × Fin N // p.1 < p.2}

/-- The type-A interval matrix: the column `(i, j)` is the coefficient vector of the positive
root `e_i - e_j = α_i + ⋯ + α_{j-1}` in the simple roots `α_k = e_k - e_{k+1}`, `k < N - 1`,
so it is `1` in the rows `i ≤ k < j` and `0` elsewhere. -/
def intervalMatrix (N : ℕ) : Matrix (Fin (N - 1)) (PositiveInterval N) ℤ :=
  of fun k p ↦ if (p.val.1 : ℕ) ≤ k ∧ (k : ℕ) < p.val.2 then 1 else 0

/-- The entry of the interval matrix in row `k` and column `(i, j)` is `1` if `i ≤ k < j` and `0`
otherwise. -/
@[simp]
theorem intervalMatrix_apply (N : ℕ) (k : Fin (N - 1)) (p : PositiveInterval N) :
    intervalMatrix N k p = if (p.val.1 : ℕ) ≤ k ∧ (k : ℕ) < p.val.2 then 1 else 0 :=
  (rfl)

/-- The column `p = (i, j)` of the interval matrix is the indicator of the interval of rows
`i ≤ k < j`. -/
theorem intervalMatrix_apply_eq_indicator (N : ℕ) (k : Fin (N - 1)) (p : PositiveInterval N) :
    intervalMatrix N k p = (Fin.val ⁻¹' Set.Ico (p.val.1 : ℕ) p.val.2).indicator 1 k := by
  classical
  rw [Set.indicator_apply]
  simp

/-- **The interval matrix is totally unimodular**: every square minor of `intervalMatrix N` is
`0`, `1` or `-1`. -/
theorem intervalMatrix_isTotallyUnimodular (N : ℕ) : (intervalMatrix N).IsTotallyUnimodular :=
  isTotallyUnimodular_of_col_eq_indicator_ordConnected fun p ↦
    ⟨_, Set.ordConnected_Ico.preimage_mono Fin.val_strictMono.monotone,
      (intervalMatrix_apply_eq_indicator N · p)⟩

/-- The simple root `α_k = e_k - e_{k+1}` as a positive root, for `k < N - 1`. -/
def simpleInterval (N : ℕ) (k : Fin (N - 1)) : PositiveInterval N :=
  ⟨(⟨k, by omega⟩, ⟨k + 1, by omega⟩), Fin.lt_def.2 (Nat.lt_succ_self _)⟩

/-- The simple root `α_k` is `e_k - e_{k+1}`: its first index is `k`. -/
@[simp]
theorem simpleInterval_fst (N : ℕ) (k : Fin (N - 1)) : ((simpleInterval N k).val.1 : ℕ) = k :=
  (rfl)

/-- The simple root `α_k` is `e_k - e_{k+1}`: its second index is `k + 1`. -/
@[simp]
theorem simpleInterval_snd (N : ℕ) (k : Fin (N - 1)) :
    ((simpleInterval N k).val.2 : ℕ) = k + 1 :=
  (rfl)

/-- The columns of the simple roots form the identity matrix: the coefficient vector of `α_k` in
the simple roots is the `k`-th standard basis vector. Thus the interval matrix has an identity
maximal minor. -/
@[simp]
theorem intervalMatrix_submatrix_simpleInterval (N : ℕ) :
    (intervalMatrix N).submatrix id (simpleInterval N) = 1 := by
  ext k l
  simp only [Matrix.submatrix_apply, id_eq, intervalMatrix_apply, simpleInterval_fst,
    simpleInterval_snd, Matrix.one_apply, Fin.ext_iff]
  split_ifs <;> omega

/-- The all-ones covector applied to the column `(i, j)` of the interval matrix is `j - i`, the
height of the positive root `e_i - e_j`. -/
theorem sum_intervalMatrix_apply (N : ℕ) (p : PositiveInterval N) :
    ∑ k, intervalMatrix N k p = (p.val.2 : ℤ) - p.val.1 := by
  have hp : (p.val.1 : ℕ) < p.val.2 := p.property
  have hj : (p.val.2 : ℕ) ≤ N - 1 := by omega
  simp only [intervalMatrix_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ if (p.val.1 : ℕ) ≤ k ∧ k < p.val.2 then (1 : ℤ) else 0),
    Finset.sum_boole]
  have hfilter : {k ∈ Finset.range (N - 1) | (p.val.1 : ℕ) ≤ k ∧ k < p.val.2} =
      Finset.Ico (p.val.1 : ℕ) p.val.2 := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hfilter, Nat.card_Ico, Nat.cast_sub hp.le]

/-- The all-ones covector is positive on every column of the interval matrix. -/
theorem sum_intervalMatrix_apply_pos (N : ℕ) (p : PositiveInterval N) :
    0 < ∑ k, intervalMatrix N k p := by
  rw [sum_intervalMatrix_apply, sub_pos, Nat.cast_lt]
  exact p.property

end TauCeti
