/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite sums over filters

This file records elementary consequences of a finite family being zero away from an initial
interval.  They are useful whenever a filtered finite sum is evaluated after all of its nonzero
terms have been passed.

It also gives positivity of the sum of a positive family over all indices except one, when the
index type has at least two elements.
-/

public section

namespace Finset

/-- For a positive family on a finite type with at least two elements, the sum over all indices
other than a given one is positive. -/
theorem sum_filter_ne_pos {ι M : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    [AddCommMonoid M] [Preorder M] [IsOrderedCancelAddMonoid M] [AddLeftStrictMono M] {a : ι → M}
    (ha : ∀ i, 0 < a i) (i : ι) : 0 < ∑ j with j ≠ i, a j := by
  obtain ⟨j, hj⟩ := exists_ne i
  exact Finset.sum_pos (fun k _ ↦ ha k) ⟨j, by simpa using hj⟩

variable {ι α M : Type*} [DecidableEq α] [AddCommMonoid M] {a : ι → α} {e : ι → M} {p q : α}

/-- If the indexing function is injective, the filtered sum over the index `a k` is the single
term `e k`, so a strict lower bound on `e k` is one on the sum. -/
theorem lt_sum_filter_eq_of_injective [Fintype ι] [LT M] {c : M} (ha : Function.Injective a)
    (k : ι) (hc : c < e k) : c < ∑ l with a l = a k, e l := by
  classical
  convert hc using 1
  rw [Finset.sum_eq_single_of_mem k (by simp)]
  intro l hl hlk
  exact absurd (ha (Finset.mem_filter.1 hl).2) hlk

/-- If all nonzero terms of a finite family have indices at or to the left of `p`, then its sum
over the terms indexed by `q` vanishes whenever `q ≤ p` fails, for instance when `p < q`. -/
theorem sum_filter_eq_zero_of_forall_ne_zero_le [LE α] (s : Finset ι) (hqp : ¬q ≤ p)
    (ha : ∀ i ∈ s, e i ≠ 0 → a i ≤ p) :
    ∑ i ∈ s with a i = q, e i = 0 :=
  sum_eq_zero fun i hi ↦ by_contra fun hei ↦
    hqp <| (mem_filter.1 hi).2 ▸ ha i (mem_filter.1 hi).1 hei

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

end Finset
