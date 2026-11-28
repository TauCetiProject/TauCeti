/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Count
public import Mathlib.Order.Interval.Finset.Nat

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
  · have hsplit : {n ∈ range (u + 1) | p n} = {n ∈ range l | p n} ∪ {n ∈ Icc l u | p n} := by
      ext n
      simp only [mem_filter, mem_range, mem_union, mem_Icc]
      constructor
      · rintro ⟨hn, hpn⟩
        rcases lt_or_ge n l with h' | h'
        · exact Or.inl ⟨h', hpn⟩
        · exact Or.inr ⟨⟨h', by omega⟩, hpn⟩
      · rintro (⟨hn, hpn⟩ | ⟨hn, hpn⟩) <;> exact ⟨by omega, hpn⟩
    have hdisj : Disjoint {n ∈ range l | p n} {n ∈ Icc l u | p n} :=
      disjoint_filter_filter (disjoint_left.2 fun n hn hn' ↦ by
        rw [mem_range] at hn
        rw [mem_Icc] at hn'
        omega)
    rw [hsplit, card_union_of_disjoint hdisj, Nat.add_sub_cancel_left]
  · rw [Icc_eq_empty (by omega), filter_empty, card_empty, eq_comm, Nat.sub_eq_zero_iff_le]
    exact card_le_card (filter_subset_filter _ (range_mono (by omega)))

end Nat
