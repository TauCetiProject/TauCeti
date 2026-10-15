/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-!
# The partitions of four and five

The decreasingly sorted parts of a partition of four or five belong to the explicit lists
below. These exhaustive classifications label the small symmetric-group representations by
their Young diagrams.
-/

public section

namespace Nat.Partition

/-- The five partitions of four, written with decreasing parts. -/
theorem sort_parts_four (μ : Nat.Partition 4) :
    μ.parts.sort (· ≥ ·) = [4] ∨ μ.parts.sort (· ≥ ·) = [3, 1] ∨
      μ.parts.sort (· ≥ ·) = [2, 2] ∨ μ.parts.sort (· ≥ ·) = [2, 1, 1] ∨
      μ.parts.sort (· ≥ ·) = [1, 1, 1, 1] := by
  have hs := (Multiset.pairwise_sort μ.parts (· ≥ ·)).sortedGE
  have hp : ∀ x ∈ μ.parts.sort (· ≥ ·), 0 < x := fun x hx =>
    μ.parts_pos ((Multiset.mem_sort (· ≥ ·)).mp hx)
  have hsum : (μ.parts.sort (· ≥ ·)).sum = 4 := by
    rw [← Multiset.sum_coe, Multiset.sort_eq, μ.parts_sum]
  generalize μ.parts.sort (· ≥ ·) = w at hs hp hsum ⊢
  rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, t⟩⟩⟩⟩⟩
  all_goals simp_all [List.sortedGE_iff_pairwise]
  all_goals omega

/-- The seven partitions of five, written with decreasing parts. -/
theorem sort_parts_five (μ : Nat.Partition 5) :
    μ.parts.sort (· ≥ ·) = [5] ∨ μ.parts.sort (· ≥ ·) = [4, 1] ∨
      μ.parts.sort (· ≥ ·) = [3, 2] ∨ μ.parts.sort (· ≥ ·) = [3, 1, 1] ∨
      μ.parts.sort (· ≥ ·) = [2, 2, 1] ∨ μ.parts.sort (· ≥ ·) = [2, 1, 1, 1] ∨
      μ.parts.sort (· ≥ ·) = [1, 1, 1, 1, 1] := by
  have hs := (Multiset.pairwise_sort μ.parts (· ≥ ·)).sortedGE
  have hp : ∀ x ∈ μ.parts.sort (· ≥ ·), 0 < x := fun x hx =>
    μ.parts_pos ((Multiset.mem_sort (· ≥ ·)).mp hx)
  have hsum : (μ.parts.sort (· ≥ ·)).sum = 5 := by
    rw [← Multiset.sum_coe, Multiset.sort_eq, μ.parts_sum]
  generalize μ.parts.sort (· ≥ ·) = w at hs hp hsum ⊢
  rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, t⟩⟩⟩⟩⟩⟩
  all_goals simp_all [List.sortedGE_iff_pairwise]
  all_goals omega

end Nat.Partition
