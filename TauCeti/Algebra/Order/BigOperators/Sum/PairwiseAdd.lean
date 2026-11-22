/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max

/-!
# Sums of families with nonnegative pairwise sums

If any two distinct members of a finite family in a linearly ordered additive group have
nonnegative sum, then so does the whole family, unless it has exactly one member. This is the
step from a two-term positivity condition to a positivity condition on a sum of many terms, as in
the passage from 2-nonnegative curvature operators to nonnegative Ricci curvature.

## Main results

* `Finset.sum_nonneg_of_pairwise_add_nonneg`.
-/

public section

namespace Finset

/-- If any two distinct members of a finite family have nonnegative sum, the sum of the family is
nonnegative, provided the family does not have exactly one member. The hypothesis on the
cardinality cannot be dropped: a single negative member has no partner. -/
theorem sum_nonneg_of_pairwise_add_nonneg {ι M : Type*} [AddCommGroup M] [LinearOrder M]
    [IsOrderedAddMonoid M] {s : Finset ι} {f : ι → M} (hs : s.card ≠ 1)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 0 ≤ f i + f j) : 0 ≤ ∑ i ∈ s, f i := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨i, hi, hmin⟩ := s.exists_min_image f hne
  rcases le_or_gt 0 (f i) with h0 | h0
  · exact sum_nonneg fun j hj ↦ h0.trans (hmin j hj)
  -- The smallest member `f i` is negative: pair it with another member; every remaining member
  -- is at least `-f i > 0`.
  obtain ⟨j, hj, hji⟩ := exists_mem_ne (lt_of_le_of_ne hne.card_pos hs.symm) i
  rw [← add_sum_erase s f hi, ← add_sum_erase _ f (mem_erase.mpr ⟨hji, hj⟩), ← add_assoc]
  refine add_nonneg (h i hi j hj hji.symm) (sum_nonneg fun k hk ↦ ?_)
  have hk' := mem_erase.mp (mem_erase.mp hk).right
  exact (neg_nonneg.mpr h0.le).trans
    (neg_le_iff_add_nonneg'.mpr (h i hi k hk'.right hk'.left.symm))

end Finset
