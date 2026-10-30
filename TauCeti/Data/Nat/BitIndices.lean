/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Colex
public import Mathlib.Data.Nat.BitIndices
public import Mathlib.Data.Nat.Bitwise

/-!
# Set bits and binary finite-set codes

The increasing list of set bits of a natural number can be obtained by testing every index
below the number. Mathlib's `Finset.equivBitIndices` identifies natural numbers with finite
sets of natural numbers, using `∑ x ∈ D, 2 ^ x` as the code of a finite set `D`.

The `i`-th bit of the code `∑ j ∈ s, 2 ^ j` records whether `i ∈ s`. Bitwise union, intersection
and difference decode to the corresponding finite-set operations.
Bounded filtering keeps the requested members of a binary code, and least-element search returns
`none` precisely for the zero code.

## References

* Mathlib's `Finset.equivBitIndices` supplies the binary finite-set equivalence.
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

/-- The `i`-th bit of the binary code of `s` records whether `i ∈ s`. -/
@[simp]
theorem testBit_sum_two_pow (s : Finset ℕ) (i : ℕ) :
    (∑ j ∈ s, 2 ^ j).testBit i = decide (i ∈ s) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← mem_bitIndices, ← List.mem_toFinset,
    Finset.toFinset_bitIndices_sum_two_pow]

end Nat

namespace Finset

/-- Binary union decodes to finite-set union. -/
theorem equivBitIndices_lor (m n : ℕ) :
    equivBitIndices (m ||| n) = equivBitIndices m ∪ equivBitIndices n := by
  ext x
  simp

/-- Binary intersection decodes to finite-set intersection. -/
theorem equivBitIndices_land (m n : ℕ) :
    equivBitIndices (m &&& n) = equivBitIndices m ∩ equivBitIndices n := by
  ext x
  simp

/-- Binary difference decodes to finite-set difference. -/
theorem equivBitIndices_ldiff (m n : ℕ) :
    equivBitIndices (Nat.ldiff m n) = equivBitIndices m \ equivBitIndices n := by
  ext x
  simp [Nat.testBit_ldiff]

end Finset

namespace Nat

/-- Keep the members of the binary-coded finite set `n` that lie below `b` and satisfy `p`. -/
def filterBitIndices (n b : ℕ) (p : ℕ → Bool) : ℕ :=
  Finset.equivBitIndices.symm ((Finset.equivBitIndices n).filter (fun x => x < b ∧ p x))

/-- Decoding bounded filtering gives the corresponding filtered finite set. -/
theorem equivBitIndices_filterBitIndices (n b : ℕ) (p : ℕ → Bool) :
    Finset.equivBitIndices (filterBitIndices n b p) =
      (Finset.equivBitIndices n).filter (fun x => x < b ∧ p x) :=
  Finset.equivBitIndices.apply_symm_apply _

/-- The result of bounded filtering contains exactly the requested members. -/
@[simp]
theorem testBit_filterBitIndices (n b x : ℕ) (p : ℕ → Bool) :
    (filterBitIndices n b p).testBit x = (n.testBit x && decide (x < b) && p x) := by
  rw [Bool.eq_iff_iff]
  simpa [and_assoc] using Finset.ext_iff.mp (equivBitIndices_filterBitIndices n b p) x

/-- The least member of a binary-coded finite set, or `none` for the empty set. -/
def leastBitIndex (n : ℕ) : Option ℕ := n.bitIndices.head?

/-- Least-element search is the head of the increasing list of set bits. -/
theorem leastBitIndex_def (n : ℕ) : leastBitIndex n = n.bitIndices.head? := by
  unfold leastBitIndex
  rfl

/-- Least-element search succeeds precisely at a member below every other member. -/
@[simp]
theorem leastBitIndex_eq_some_iff (n k : ℕ) :
    leastBitIndex n = some k ↔ k ∈ Finset.equivBitIndices n ∧
      ∀ x ∈ Finset.equivBitIndices n, k ≤ x := by
  have hs := n.bitIndices_sorted.pairwise
  cases h : n.bitIndices with
  | nil => simp [leastBitIndex, h]
  | cons a l =>
    rw [h, List.pairwise_cons] at hs
    simp only [leastBitIndex, List.head?_cons, Option.some.injEq,
      Finset.equivBitIndices_apply, h, List.mem_toFinset, List.mem_cons]
    constructor
    · rintro rfl
      exact ⟨Or.inl rfl, fun x hx => hx.elim (fun h => h.ge) (fun h => (hs.1 x h).le)⟩
    · rintro ⟨hk, hmin⟩
      exact le_antisymm (hk.elim (fun h => h.ge) (fun h => (hs.1 k h).le))
        (hmin a (Or.inl rfl))

/-- Least-element search returns `none` exactly for the zero code. -/
@[simp]
theorem leastBitIndex_eq_none_iff (n : ℕ) : leastBitIndex n = none ↔ n = 0 := by
  simp only [leastBitIndex, List.head?_eq_none_iff]
  constructor
  · intro h
    simpa [h] using (sum_map_two_pow_bitIndices n).symm
  · rintro rfl
    exact bitIndices_zero

end Nat
