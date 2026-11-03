/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Young.YoungDiagram
public import TauCeti.GroupTheory.Perm.Inversion
import TauCeti.Combinatorics.Young.Diagram

/-!
# The shuffle of a Young diagram in a box

Let `μ` be a Young diagram that fits in the box with `m` rows and `n` columns.  The `m` numbers
`μ_{m-1-k} + k` for `k < m` and the `n` numbers `m + j - μ'ⱼ` for `j < n` are complementary in
`{0, …, m + n - 1}` (Macdonald (I.1.7)); the first family is the list of beta-numbers
`YoungDiagram.betaNumber μ m` read upwards.  Listing the first family and then the second is a
permutation of `{0, …, m + n - 1}`, the **box shuffle** of `μ`.  Each family increases, and an
index `k < m` and an index `m + j` are out of order exactly when the cell `(m - 1 - k, j)` lies in
`μ`.  So the inversions of the box shuffle are in bijection with the cells of `μ`, and its sign is
`(-1)^{|μ|}`.

This is the combinatorial input to the dual Jacobi--Trudi identity
`TauCeti.diagramSchurPoly_eq_det_esymmInt`.

## Main definitions

* `YoungDiagram.boxShuffle`: the box shuffle of `μ` with respect to `m` rows, as a function
  `ℕ → ℕ`.
* `YoungDiagram.boxShufflePerm`: the box shuffle of `μ` in the `m × n` box, as a permutation of
  `Fin (m + n)`.

## Main results

* `YoungDiagram.boxShuffle_lt_boxShuffle_iff`: the inversions of the box shuffle are the cells of
  `μ`.
* `YoungDiagram.card_inversions_boxShufflePerm`: the box shuffle has `|μ|` inversions.
* `YoungDiagram.sign_boxShufflePerm`: the sign of the box shuffle is `(-1)^{|μ|}`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  (1.7).
-/

public section

namespace YoungDiagram

open Finset

section BoxShuffle

variable (μ : YoungDiagram) (m : ℕ)

/-- The box shuffle attached to a diagram `μ` with at most `m` rows: an index `k < m` goes to
`μ_{m-1-k} + k`, and an index `m + j` goes to `m + j - μ'ⱼ`. -/
def boxShuffle (k : ℕ) : ℕ :=
  if k < m then μ.rowLen (m - (k + 1)) + k else k - μ.colLen (k - m)

theorem boxShuffle_def (k : ℕ) :
    μ.boxShuffle m k = if k < m then μ.rowLen (m - (k + 1)) + k else k - μ.colLen (k - m) :=
  (rfl)

/-- An index `k < m` and an index `k' ≥ m` whose cell `(m - 1 - k, k' - m)` lies in the diagram
are an inversion of the box shuffle. -/
private theorem boxShuffle_lt_boxShuffle_of_mem {k k' : ℕ} (hk : k < m) (hk' : m ≤ k')
    (hmem : (m - (k + 1), k' - m) ∈ μ) : μ.boxShuffle m k' < μ.boxShuffle m k := by
  have hrow := mem_iff_lt_rowLen.mp hmem
  have hcol := mem_iff_lt_colLen.mp hmem
  simp only [boxShuffle, hk, show ¬k' < m by omega, ↓reduceIte]
  omega

/-- Every other pair of indices `k < k'` is ordered by the box shuffle: within the first `m`
indices and within the rest the box shuffle increases, and across them it increases unless the
corresponding cell lies in the diagram. -/
private theorem boxShuffle_lt_boxShuffle_of_not {k k' : ℕ} (hm : μ.colLen 0 ≤ m) (hkk' : k < k')
    (h : ¬(k < m ∧ m ≤ k' ∧ (m - (k + 1), k' - m) ∈ μ)) :
    μ.boxShuffle m k < μ.boxShuffle m k' := by
  have hcol : ∀ j, μ.colLen j ≤ m := fun j ↦ (μ.colLen_anti 0 j j.zero_le).trans hm
  by_cases hk' : k' < m
  · have := μ.rowLen_anti (m - (k' + 1)) (m - (k + 1)) (by omega)
    simp only [boxShuffle, hk', hkk'.trans hk', ↓reduceIte]
    omega
  by_cases hk : k < m
  · have hmem : (m - (k + 1), k' - m) ∉ μ := fun hmem ↦ h ⟨hk, by omega, hmem⟩
    have hrow := mt mem_iff_lt_rowLen.mpr hmem
    have hcol' := mt mem_iff_lt_colLen.mpr hmem
    have := hcol (k' - m)
    simp only [boxShuffle, hk, hk', ↓reduceIte]
    omega
  · have := μ.colLen_anti (k - m) (k' - m) (by omega)
    have := hcol (k - m)
    simp only [boxShuffle, hk, hk', ↓reduceIte]
    omega

/-- **The inversions of the box shuffle are the cells of the diagram** (Macdonald (I.1.7)). -/
theorem boxShuffle_lt_boxShuffle_iff {k k' : ℕ} (hm : μ.colLen 0 ≤ m) (hkk' : k < k') :
    μ.boxShuffle m k' < μ.boxShuffle m k ↔ k < m ∧ m ≤ k' ∧ (m - (k + 1), k' - m) ∈ μ :=
  ⟨fun hlt ↦ by_contra fun h ↦ (boxShuffle_lt_boxShuffle_of_not μ m hm hkk' h).not_gt hlt,
    fun ⟨hk, hk', hmem⟩ ↦ boxShuffle_lt_boxShuffle_of_mem μ m hk hk' hmem⟩

private theorem boxShuffle_ne_boxShuffle (hm : μ.colLen 0 ≤ m) {k k' : ℕ} (hkk' : k < k') :
    μ.boxShuffle m k' ≠ μ.boxShuffle m k := by
  by_cases h : k < m ∧ m ≤ k' ∧ (m - (k + 1), k' - m) ∈ μ
  · exact (boxShuffle_lt_boxShuffle_of_mem μ m h.1 h.2.1 h.2.2).ne
  · exact (boxShuffle_lt_boxShuffle_of_not μ m hm hkk' h).ne'

private theorem boxShuffle_lt {n k : ℕ} (hn : μ.rowLen 0 ≤ n) (hk : k < m + n) :
    μ.boxShuffle m k < m + n := by
  have := μ.rowLen_anti 0 (m - (k + 1)) (Nat.zero_le _)
  unfold boxShuffle
  split_ifs <;> omega

variable {μ m} {n : ℕ}

/-- The box shuffle of a diagram in the box with `m` rows and `n` columns, as a permutation of
`Fin (m + n)`. -/
noncomputable def boxShufflePerm (hm : μ.colLen 0 ≤ m) (hn : μ.rowLen 0 ≤ n) :
    Equiv.Perm (Fin (m + n)) :=
  Equiv.ofBijective (fun k ↦ ⟨μ.boxShuffle m k, boxShuffle_lt μ m hn k.isLt⟩) <|
    Finite.injective_iff_bijective.mp fun a b hab ↦ by
      by_contra hne
      have hab' : μ.boxShuffle m a = μ.boxShuffle m b := congrArg Fin.val hab
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
      · exact boxShuffle_ne_boxShuffle μ m hm h hab'.symm
      · exact boxShuffle_ne_boxShuffle μ m hm h hab'

@[simp]
theorem boxShufflePerm_apply_val (hm : μ.colLen 0 ≤ m) (hn : μ.rowLen 0 ≤ n)
    (k : Fin (m + n)) : (boxShufflePerm hm hn k : ℕ) = μ.boxShuffle m k :=
  (rfl)

/-- The box shuffle has one inversion for each cell of the diagram. -/
@[simp]
theorem card_inversions_boxShufflePerm (hm : μ.colLen 0 ≤ m) (hn : μ.rowLen 0 ≤ n) :
    #(univ.inversions (boxShufflePerm hm hn)) = μ.card := by
  refine card_nbij (fun p ↦ (m - ((p.1 : ℕ) + 1), (p.2 : ℕ) - m)) ?_ ?_ ?_
  · rintro ⟨x, y⟩ hp
    simp only [mem_coe, mem_inversions, mem_univ, true_and, Fin.lt_def,
      boxShufflePerm_apply_val] at hp
    exact (mem_cells _).mpr ((boxShuffle_lt_boxShuffle_iff μ m hm hp.1).mp hp.2).2.2
  · rintro ⟨x, y⟩ hp ⟨x', y'⟩ hp' hxy
    simp only [mem_coe, mem_inversions, mem_univ, true_and, Fin.lt_def,
      boxShufflePerm_apply_val] at hp hp'
    have h := (boxShuffle_lt_boxShuffle_iff μ m hm hp.1).mp hp.2
    have h' := (boxShuffle_lt_boxShuffle_iff μ m hm hp'.1).mp hp'.2
    simp only [Prod.mk.injEq] at hxy
    rw [Prod.mk.injEq, Fin.ext_iff, Fin.ext_iff]
    omega
  · rintro ⟨i, j⟩ hc
    have hc' : (i, j) ∈ μ := (mem_cells _).mp hc
    have hi : i < m := (lt_colLen_zero_of_mem hc').trans_le hm
    have hj : j < n := (mem_iff_lt_rowLen.mp hc').trans_le
      ((μ.rowLen_anti 0 i i.zero_le).trans hn)
    refine ⟨(⟨m - (i + 1), by omega⟩, ⟨m + j, by omega⟩), ?_, ?_⟩
    · simp only [mem_coe, mem_inversions, mem_univ, true_and, Fin.lt_def,
        boxShufflePerm_apply_val]
      refine ⟨by omega,
        (boxShuffle_lt_boxShuffle_iff μ m hm (by omega)).mpr ⟨by omega, by omega, ?_⟩⟩
      simpa only [show m - (m - (i + 1) + 1) = i by omega, Nat.add_sub_cancel_left] using hc'
    · simp only [Prod.mk.injEq]
      omega

/-- The sign of the box shuffle is `(-1)` to the number of cells of the diagram. -/
@[simp]
theorem sign_boxShufflePerm (hm : μ.colLen 0 ≤ m) (hn : μ.rowLen 0 ≤ n) :
    Equiv.Perm.sign (boxShufflePerm hm hn) = (-1) ^ μ.card := by
  rw [TauCeti.sign_eq_neg_one_pow_card_inversion, card_inversions_boxShufflePerm]

end BoxShuffle

end YoungDiagram
