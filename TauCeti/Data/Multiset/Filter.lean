/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Multiset.Filter

/-!
# Filtering a finite sum of multisets

Filtering a multiset is additive, so it distributes over a finite sum of multisets. Mathlib
records the binary case as `Multiset.filter_add`; this file records the finite-sum case, used to
recover the part of a concatenated unordered tuple lying in a given set from the parts of its
summands.
-/

public section

namespace Multiset

variable {α ι : Type*} (p : α → Prop) [DecidablePred p]

/-- Filtering distributes over a finite sum of multisets. -/
@[simp]
theorem filter_sum (s : Finset ι) (f : ι → Multiset α) :
    filter p (∑ i ∈ s, f i) = ∑ i ∈ s, filter p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, filter_add, ih, Finset.sum_insert ha]

end Multiset
