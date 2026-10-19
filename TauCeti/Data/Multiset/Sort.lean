/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Multiset.Sort

/-!
# Sorting a sum of separated multisets

If every element of a multiset `s` precedes every element of a multiset `t`, then sorting `s + t`
lists the sorted elements of `s` followed by the sorted elements of `t`. This is how an ordered
monomial over an ordered disjoint union of index sets splits into a product of ordered monomials
over the two pieces.
-/

public section

namespace Multiset

variable {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [Std.Antisymm r]
  [Std.Total r]

/-- Sorting the sum of two multisets, every element of the first related to every element of the
second, appends the two sorted lists. -/
theorem sort_add {s t : Multiset α} (h : ∀ a ∈ s, ∀ b ∈ t, r a b) :
    (s + t).sort r = s.sort r ++ t.sort r := by
  refine List.Perm.eq_of_pairwise' (r := r) (pairwise_sort _ _) ?_ ?_
  · exact List.pairwise_append.2 ⟨pairwise_sort _ _, pairwise_sort _ _,
      fun a ha b hb ↦ h a ((mem_sort _).1 ha) b ((mem_sort _).1 hb)⟩
  · rw [← coe_eq_coe, ← coe_add, sort_eq, sort_eq, sort_eq]

end Multiset
