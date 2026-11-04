/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Card
public import TauCeti.Combinatorics.Enumerative.Partition.Conjugate

/-!
# Pairwise row minima and column squares

For a finite family of row lengths, the sum of pairwise minima equals the sum of the
squares of the column lengths. No ordering of the rows is required. In particular this
converts blockwise centralizer dimensions into the usual formula in the conjugate partition.

For a partition `μ` of `n`, the sum of the squares of the parts of its conjugate `μ'` exceeds
`n` by twice the number of pairs of cells in a common column. So it is at least `n` (as for
any partition of `n`), with equality exactly for the one-row partition `(n)`. It never equals
`n + 1`, and it equals `n + 2` exactly for the partition `(n - 1, 1)`. Since
`∑ⱼ (μ'ⱼ)²` is the centralizer dimension of a nilpotent endomorphism of Jordan type `μ`, these
are the two smallest centralizer dimensions, attained by the regular and subregular Jordan types.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  §6.1: centralizer dimensions in terms of the conjugate partition.
-/

public section

namespace Finset

/-- Double counting pairs of cells in the same column converts pairwise minima of
row lengths into squares of column lengths. The bound may exceed every row length. -/
theorem sum_sum_min_eq_sum_sq_card_filter {ι : Type*} (s : Finset ι) (len : ι → ℕ)
    (n : ℕ) (hlen : ∀ i ∈ s, len i ≤ n) :
    (∑ i ∈ s, ∑ j ∈ s, min (len i) (len j)) =
      ∑ k ∈ range n, (s.filter fun i => k < len i).card ^ 2 := by
  classical
  have hmin (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      min (len i) (len j) =
        ∑ k ∈ range n, (if k < len i then 1 else 0) * (if k < len j then 1 else 0) := by
    have hf : ((range n).filter fun k => k < len i ∧ k < len j) =
        range (min (len i) (len j)) := by
      ext k
      simp only [mem_filter, mem_range, lt_min_iff]
      have := hlen i hi
      omega
    symm
    calc
      _ = ((range n).filter fun k => k < len i ∧ k < len j).card := by
        simp [← ite_and, sum_boole, and_comm]
      _ = _ := by rw [hf, card_range]
  rw [sum_congr rfl fun i hi => sum_congr rfl fun j hj => hmin i hi j hj]
  simp_rw [sum_comm (s := s) (t := range n)]
  apply sum_congr rfl
  intro k hk
  rw [← sum_mul_sum]
  simp [sq]

end Finset

namespace Nat.Partition

open Finset

variable {n : ℕ} (μ : n.Partition)

/-- **Column squares and pairs of cells.** The sum of the squares of the column lengths of a
partition of `n` exceeds `n` by twice the number of pairs of cells in a common column, where
column `k` has one cell for each part larger than `k`. -/
theorem sum_sq_conjugate_parts_eq_add_two_mul_sum_choose_two :
    (μ.conjugate.parts.map (· ^ 2)).sum =
      n + 2 * ∑ k ∈ range n, (μ.parts.filter (k < ·)).card.choose 2 := by
  -- Twice the number of pairs of cells in a column is the excess of its squared length.
  have hsq (x : ℕ) : x ^ 2 = x + 2 * x.choose 2 := by
    induction x with
    | zero => rfl
    | succ x ih => rw [Nat.choose_succ_succ, Nat.choose_one_right]; grind
  rw [← μ.sum_map_conjugate_parts (·.choose 2) rfl fun _ => le_of_mem_parts,
    ← Multiset.sum_map_mul_left]
  calc _ = (μ.conjugate.parts.map fun x => x + 2 * x.choose 2).sum := by
        rw [Multiset.map_congr rfl fun x _ => hsq x]
    _ = _ := by rw [Multiset.sum_map_add, Multiset.map_id', parts_sum]

/-- **The regular Jordan type.** The sum of the squares of the parts of the conjugate partition
equals `n` exactly for the one-row partition `(n)`. -/
theorem sum_sq_conjugate_parts_eq_self_iff :
    (μ.conjugate.parts.map (· ^ 2)).sum = n ↔ μ = indiscrete n := by
  rw [sum_sq_conjugate_parts_eq_add_two_mul_sum_choose_two, add_eq_left, mul_eq_zero,
    sum_eq_zero_iff]
  simp only [two_ne_zero, false_or, mem_range, Nat.choose_eq_zero_iff]
  rcases eq_or_ne n 0 with rfl | hn
  · exact iff_of_true (by simp) (Subsingleton.elim _ _)
  constructor
  · intro h
    -- A first column of length at most one forces a single part.
    have hcard : μ.parts.card ≤ 1 := by
      have := h 0 (Nat.pos_of_ne_zero hn)
      rw [filter_pos_parts] at this
      omega
    have hne : μ.parts ≠ 0 := fun h0 => hn (by rw [← μ.parts_sum, h0, Multiset.sum_zero])
    obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp
      (le_antisymm hcard (Multiset.card_pos.mpr hne))
    have hsum := μ.parts_sum
    rw [ha, Multiset.sum_singleton] at hsum
    ext1
    rw [ha, indiscrete_parts hn, hsum]
  · rintro rfl k -
    rw [indiscrete_parts hn]
    exact (Multiset.card_le_card (Multiset.filter_le _ _)).trans_lt (by simp)

/-- **The gap above the regular Jordan type.** Away from the one-row partition, the sum of the
squares of the parts of the conjugate partition is at least `n + 2`. -/
theorem add_two_le_sum_sq_conjugate_parts (h : μ ≠ indiscrete n) :
    n + 2 ≤ (μ.conjugate.parts.map (· ^ 2)).sum := by
  have h' := mt (sum_sq_conjugate_parts_eq_self_iff μ).mp h
  rw [sum_sq_conjugate_parts_eq_add_two_mul_sum_choose_two] at h' ⊢
  omega

/-- **The subregular Jordan type.** The sum of the squares of the parts of the conjugate
partition equals `n + 2` exactly for the partition `(n - 1, 1)`. -/
theorem sum_sq_conjugate_parts_eq_add_two_iff :
    (μ.conjugate.parts.map (· ^ 2)).sum = n + 2 ↔ μ.parts = {n - 1, 1} := by
  rw [sum_sq_conjugate_parts_eq_add_two_mul_sum_choose_two]
  constructor
  · intro h
    replace h : ∑ k ∈ range n, (μ.parts.filter (k < ·)).card.choose 2 = 1 := by omega
    have hsub (s : Finset ℕ) (hs : s ⊆ range n) :
        ∑ k ∈ s, (μ.parts.filter (k < ·)).card.choose 2 ≤ 1 :=
      h ▸ sum_le_sum_of_subset hs
    -- The first column has exactly two cells, so there are exactly two parts.
    have hcard : μ.parts.card = 2 := by
      rcases lt_trichotomy μ.parts.card 2 with hlt | heq | hgt
      · have : ∑ k ∈ range n, (μ.parts.filter (k < ·)).card.choose 2 = 0 :=
          sum_eq_zero fun k _ => Nat.choose_eq_zero_of_lt
            ((Multiset.card_le_card (Multiset.filter_le _ _)).trans_lt hlt)
        omega
      · exact heq
      · have hn : 0 < n := Nat.pos_of_ne_zero fun hn => by subst hn; simp at h
        have h0 := hsub {0} (by simpa using hn)
        rw [sum_singleton, filter_pos_parts] at h0
        have := Nat.choose_le_choose 2 (show 3 ≤ μ.parts.card by omega)
        simp [Nat.choose] at this
        omega
    obtain ⟨x, y, hxy⟩ := Multiset.card_eq_two.mp hcard
    have hx : 0 < x := μ.parts_pos (by simp [hxy])
    have hy : 0 < y := μ.parts_pos (by simp [hxy])
    have hsum : x + y = n := by simpa [hxy] using μ.parts_sum
    -- The second column has at most one cell, so one of the two parts is `1`.
    have h01 := hsub {0, 1} (by intro k; simp only [mem_insert, mem_singleton, mem_range]; omega)
    rw [sum_pair zero_ne_one, filter_pos_parts, hcard, Nat.choose_self] at h01
    have hxy1 : x = 1 ∨ y = 1 := by
      by_contra! hne
      have hfilter : μ.parts.filter (1 < ·) = μ.parts :=
        Multiset.filter_eq_self.mpr fun a ha => by
          rw [hxy] at ha
          simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at ha
          omega
      rw [hfilter, hcard, Nat.choose_self] at h01
      omega
    rw [hxy]
    rcases hxy1 with rfl | rfl
    · rw [Multiset.pair_comm, show y = n - 1 by omega]
    · rw [show x = n - 1 by omega]
  · intro h
    have hn : 2 ≤ n := by
      have := μ.parts_pos (show n - 1 ∈ μ.parts by simp [h])
      omega
    suffices ∑ k ∈ range n, (μ.parts.filter (k < ·)).card.choose 2 = 1 by omega
    rw [sum_eq_single 0]
    · rw [filter_pos_parts, h]
      simp
    · intro k _ hk
      apply Nat.choose_eq_zero_of_lt
      rw [h, Multiset.insert_eq_cons, Multiset.filter_cons, Multiset.filter_singleton]
      split_ifs <;> first | omega | simp
    · intro h0
      simp at h0
      omega

end Nat.Partition
