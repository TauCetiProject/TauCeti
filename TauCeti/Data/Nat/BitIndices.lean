/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Colex
public import Mathlib.Data.Finset.Sort

/-!
# Bit indices and the binary code of a finite set

Mathlib's `Finset.equivBitIndices` identifies a finite set `s` of naturals with its binary code
`∑ i ∈ s, 2 ^ i`, and decodes a number `n` as the set of its bit indices `n.bitIndices`. This file
relates the code to the binary digits and to sorting: the `i`-th bit of the code of `s` records
whether `i ∈ s`, the bit indices of the code of `s` are the elements of `s` in increasing order, and
the bit indices of `n` are the numbers below `n` whose bit is set.

## Main results

* `Nat.testBit_sum_two_pow`: the `i`-th bit of `∑ j ∈ s, 2 ^ j` is `decide (i ∈ s)`.
* `Nat.bitIndices_sum_two_pow`: the bit indices of `∑ i ∈ s, 2 ^ i` are `s.sort`.
* `Nat.bitIndices_eq_filter_range`: the bit indices of `n` are the numbers `i < n` with
  `n.testBit i`.
-/

public section

namespace Nat

/-- The `i`-th bit of the binary code of `s` records whether `i ∈ s`. -/
@[simp]
theorem testBit_sum_two_pow (s : Finset ℕ) (i : ℕ) :
    (∑ j ∈ s, 2 ^ j).testBit i = decide (i ∈ s) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← mem_bitIndices, ← List.mem_toFinset,
    Finset.toFinset_bitIndices_sum_two_pow]

/-- Sorting the set of bit indices of `n` recovers the list of bit indices. -/
@[simp]
theorem sort_toFinset_bitIndices (n : ℕ) : n.bitIndices.toFinset.sort = n.bitIndices :=
  (List.toFinset_sort _ bitIndices_nodup).2 (bitIndices_sorted.pairwise.imp le_of_lt)

/-- The bit indices of the binary code `∑ i ∈ s, 2 ^ i` are the elements of `s` in increasing
order. -/
@[simp]
theorem bitIndices_sum_two_pow (s : Finset ℕ) : (∑ i ∈ s, 2 ^ i).bitIndices = s.sort := by
  conv_lhs => rw [← s.sort_toFinset (· ≤ ·)]
  rw [List.sum_toFinset _ (s.sort_nodup _)]
  exact bitIndices_sum_map_two_pow (Finset.sortedLT_sort s)

/-- The bit indices of `n` are the numbers below `n` whose bit is set. -/
theorem bitIndices_eq_filter_range (n : ℕ) :
    n.bitIndices = (List.range n).filter (n.testBit ·) := by
  refine bitIndices_sorted.eq_of_mem_iff
    (List.sortedLT_iff_pairwise.2 ((List.sortedLT_range n).pairwise.sublist List.filter_sublist))
    fun i => ?_
  simp only [mem_bitIndices, List.mem_filter, List.mem_range, iff_and_self]
  exact fun h => i.lt_two_pow_self.trans_le (ge_two_pow_of_testBit h)

end Nat
