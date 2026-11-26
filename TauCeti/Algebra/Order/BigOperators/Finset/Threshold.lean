/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Counting threshold crossings in a finite family

If each point of a subset reaches a threshold in at least one nonnegative weight function,
then the total weight over the family bounds the cardinality times that threshold.
-/

public section

namespace Finset

/-- A counting form of Markov's inequality for a finite family of weight functions. Each term
counted by `s` reaches the common threshold `r` in at least one of the weights indexed by `I`. -/
theorem card_nsmul_le_sum_sum_of_exists_le {α ι R : Type*} [AddCommMonoid R] [PartialOrder R]
    [IsOrderedAddMonoid R] (s : Finset α) {t : Finset α} (hst : s ⊆ t) (I : Finset ι)
    (w : ι → α → R) {r : R} (hw : ∀ i ∈ I, ∀ x ∈ t, 0 ≤ w i x)
    (hr : ∀ x ∈ s, ∃ i ∈ I, r ≤ w i x) : s.card • r ≤ ∑ i ∈ I, ∑ x ∈ t, w i x := by
  calc
    _ ≤ ∑ x ∈ s, ∑ i ∈ I, w i x := s.card_nsmul_le_sum _ _ fun x hx ↦ by
      obtain ⟨i, hi, hrx⟩ := hr x hx
      exact hrx.trans (single_le_sum (fun j hj ↦ hw j hj x (hst hx)) hi)
    _ ≤ ∑ x ∈ t, ∑ i ∈ I, w i x :=
      sum_le_sum_of_subset_of_nonneg hst fun x hx _ ↦ sum_nonneg fun i hi ↦ hw i hi x hx
    _ = _ := sum_comm

end Finset
