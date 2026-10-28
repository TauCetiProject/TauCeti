/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.BitIndices

/-!
# Finding set bits by bounded filtering

The increasing list of set bits of a natural number can be obtained by testing every index
below the number. This finite-search description is useful for effective binary coding.
-/

public section

namespace Nat

/-- The set bits of `n` are found by filtering the finite interval below `n`. -/
theorem bitIndices_eq_filter_range (n : ℕ) :
    n.bitIndices = (List.range n).filter n.testBit := by
  apply bitIndices_sorted.eq_of_mem_iff ((List.sortedLT_range n).pairwise.filter _ |>.sortedLT)
  intro i
  simp only [mem_bitIndices, List.mem_filter, List.mem_range]
  exact ⟨fun h => ⟨(i.lt_two_pow_self.trans_le (ge_two_pow_of_testBit h)), h⟩,
    fun h => h.2⟩

end Nat
