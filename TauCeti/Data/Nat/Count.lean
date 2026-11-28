/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Count
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Order.SuccPred.Nat

/-!
# Counting a predicate over an interval of natural numbers

For a decidable predicate `p` on the natural numbers, `Nat.count p n` is the number of `k < n`
satisfying `p`. The number of `k` in a closed interval `[l, u]` satisfying `p` is therefore the
difference `Nat.count p (u + 1) - Nat.count p l`.

## Main results

* `Nat.card_filter_Icc_eq_count_sub`: `#{n ∈ Icc l u | p n} = Nat.count p (u + 1) - Nat.count p l`,
  with natural-number subtraction.
-/

public section

open Finset

namespace Nat

/-- The number of `n` in `[l, u]` satisfying `p` is `Nat.count p (u + 1) - Nat.count p l`, with
natural-number subtraction. For `l > u` the interval is empty and both sides are zero. -/
theorem card_filter_Icc_eq_count_sub (p : ℕ → Prop) [DecidablePred p] (l u : ℕ) :
    #{n ∈ Icc l u | p n} = count p (u + 1) - count p l := by
  rw [count_eq_card_filter_range, count_eq_card_filter_range]
  rcases le_or_gt l (u + 1) with h | h
  · rw [← Ico_add_one_right_eq_Icc l u, range_eq_Ico, range_eq_Ico,
      ← Ico_union_Ico_eq_Ico (Nat.zero_le l) h, filter_union,
      card_union_of_disjoint (disjoint_filter_filter (Ico_disjoint_Ico_consecutive 0 l (u + 1))),
      Nat.add_sub_cancel_left]
  · rw [Icc_eq_empty (by omega), filter_empty, card_empty, eq_comm, Nat.sub_eq_zero_iff_le]
    exact card_le_card (filter_subset_filter _ (range_mono (by omega)))

end Nat
