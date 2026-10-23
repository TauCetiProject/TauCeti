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

/-!
# Pairwise row minima and column squares

For a finite family of row lengths, the sum of pairwise minima equals the sum of the
squares of the column lengths. No ordering of the rows is required. In particular this
converts blockwise centralizer dimensions into the usual formula in the conjugate partition.
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
        simp_rw [ite_mul, one_mul, zero_mul, ← ite_and, sum_boole, Nat.cast_id]
      _ = _ := by rw [hf, card_range]
  simp_rw [sum_congr rfl (fun i hi => sum_congr rfl (fun j hj => hmin i hi j hj))]
  simp_rw [sum_comm (s := s) (t := range n)]
  apply sum_congr rfl
  intro k hk
  rw [← sum_mul_sum]
  simp [sq]

end Finset
