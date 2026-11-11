/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import TauCeti.Algebra.BigOperators.Finset.Filter

/-!
# Finite sums over filters

This file records elementary consequences of a finite family being zero away from an initial
interval.  They are useful whenever a filtered finite sum is evaluated after all of its nonzero
terms have been passed.

It also gives positivity of the sum of a positive family over all indices except one, when the
index type has at least two elements, and bounds the sum of a nonnegative family on `ℕ` that is
bounded by `C` and vanishes outside the window `|j - k| < L` by `(2 * L) • C`
(`Finset.sum_le_of_eq_zero_of_dist_ge`).
-/

public section

namespace Finset

/-- For a positive family on a finite type with at least two elements, the sum over all indices
other than a given one is positive. -/
theorem sum_filter_ne_pos {ι M : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    [AddCommMonoid M] [Preorder M] [AddLeftStrictMono M] {a : ι → M}
    (ha : ∀ i, 0 < a i) (i : ι) : 0 < ∑ j with j ≠ i, a j := by
  obtain ⟨j, hj⟩ := exists_ne i
  suffices ∀ t : Finset ι, t.Nonempty → 0 < ∑ k ∈ t, a k from this _ ⟨j, by simpa using hj⟩
  intro t ht
  induction ht using Finset.Nonempty.cons_induction with
  | singleton k => simpa using ha k
  | cons k t hk _ ih => rw [sum_cons]; exact (ha k).trans (lt_add_of_pos_right _ ih)

variable {ι α M : Type*} [DecidableEq α] [AddCommMonoid M] {a : ι → α} {e : ι → M} {p q : α}

/-- If all nonzero terms of a finite family have indices at or to the left of `p`, then its sum
over the terms indexed by `q` vanishes whenever `q ≤ p` fails, for instance when `p < q`. -/
theorem sum_filter_eq_zero_of_forall_ne_zero_le [LE α] (s : Finset ι) (hqp : ¬q ≤ p)
    (ha : ∀ i ∈ s, e i ≠ 0 → a i ≤ p) :
    ∑ i ∈ s with a i = q, e i = 0 :=
  sum_filter_eq_zero_of_ne fun i hi hei hq ↦ hqp (hq ▸ ha i hi hei)

/-- If all nonzero terms of a finite family have indices at or to the left of `p`, then a filtered
sum at or beyond `p` is bounded below by any negative `c` that also bounds the sum at `p` from
below. -/
theorem lt_sum_filter_of_lt_zero_of_forall_ne_zero_le [PartialOrder α] [LT M] (s : Finset ι)
    {c : M} (hc : c < 0) (hp : c < ∑ i ∈ s with a i = p, e i)
    (ha : ∀ i ∈ s, e i ≠ 0 → a i ≤ p) (hpq : p ≤ q) :
    c < ∑ i ∈ s with a i = q, e i := by
  obtain rfl | hpq := hpq.eq_or_lt
  · exact hp
  · rwa [sum_filter_eq_zero_of_forall_ne_zero_le s hpq.not_ge ha]

/-- A family of nonnegative terms bounded by `C`, all of which vanish outside the indices `k` with
`|j - k| < L`, has sum at most `(2 * L) • C` over any finite set. -/
theorem sum_le_of_eq_zero_of_dist_ge [PartialOrder M] [IsOrderedAddMonoid M] {f : ℕ → M} {C : M}
    {j L : ℕ} (hf : ∀ k, 0 ≤ f k) (hC : ∀ k, f k ≤ C)
    (hzero : ∀ k, j + L ≤ k ∨ k + L ≤ j → f k = 0) (s : Finset ℕ) :
    ∑ k ∈ s, f k ≤ (2 * L) • C := by
  have hcard : #(Ico (j - L) (j + L)) ≤ 2 * L := by simp only [Nat.card_Ico]; omega
  calc ∑ k ∈ s, f k = ∑ k ∈ s with k ∈ Ico (j - L) (j + L), f k :=
        (sum_filter_of_ne fun k _ h ↦ by_contra fun hk ↦ h (hzero k (by
          simp only [mem_Ico, not_and_or, not_le, not_lt] at hk; omega))).symm
    _ ≤ ∑ k ∈ Ico (j - L) (j + L), f k :=
        sum_le_sum_of_subset_of_nonneg (fun k hk ↦ (mem_filter.1 hk).2) fun k _ _ ↦ hf k
    _ ≤ #(Ico (j - L) (j + L)) • C := sum_le_card_nsmul _ _ _ fun k _ ↦ hC k
    _ ≤ (2 * L) • C := nsmul_le_nsmul_left ((hf 0).trans (hC 0)) hcard

end Finset
