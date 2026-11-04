/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Finite sums over filters

This file records elementary consequences of a finite family being zero away from an initial
interval.  They are useful whenever a filtered finite sum is evaluated after all of its nonzero
terms have been passed.

It also gives positivity of the sum of a positive family over all indices except one, when the
index type has at least two elements.
-/

public section

open Set
open scoped BigOperators

namespace Finset

/-- For a positive family on a finite type with at least two elements, the sum over all indices
other than a given one is positive. -/
theorem sum_filter_ne_pos {ι M : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    [AddCommMonoid M] [Preorder M] [IsOrderedCancelAddMonoid M] [AddLeftStrictMono M] {a : ι → M}
    (ha : ∀ i, 0 < a i) (i : ι) : 0 < ∑ j with j ≠ i, a j := by
  obtain ⟨j, hj⟩ := exists_ne i
  exact Finset.sum_pos (fun k _ ↦ ha k) ⟨j, by simpa using hj⟩

variable {ι α M : Type*} [Preorder α] [AddCommMonoid M]

open scoped Classical in
/-- If all nonzero terms of a finite family have indices at or to the left of `p`, then its sum
over the terms indexed by `q` vanishes whenever `p < q`. -/
theorem sum_filter_eq_zero_of_forall_ne_zero_le (s : Finset ι) {a : ι → α}
    {e : ι → M} {p q : α} (hpq : p < q) (ha : ∀ i ∈ s, e i ≠ 0 → a i ≤ p) :
    Finset.sum (s.filter (fun i => a i = q)) e = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  by_contra hei
  have hai := ha i (Finset.mem_filter.mp hi).1 hei
  exact (not_lt_of_ge hai) ((Finset.mem_filter.mp hi).2 ▸ hpq)

open scoped Classical in
/-- If all nonzero terms of a finite family have indices at or to the left of `p`, then a filtered
sum beyond `p` is bounded below by any negative `c` that also bounds the sum at `p` from below. -/
theorem lt_sum_filter_of_lt_zero_of_forall_ne_zero_le {γ β : Type*} [PartialOrder γ]
    [LT β] [AddCommMonoid β] (s : Finset ι) {a : ι → γ} {e : ι → β}
    {p : γ} {c : β} (hc : c < 0)
    (hp : c < Finset.sum (s.filter (fun i => a i = p)) e)
    (ha : ∀ i ∈ s, e i ≠ 0 → a i ≤ p) :
    ∀ {q : γ}, p ≤ q → c < Finset.sum (s.filter (fun i => a i = q)) e := by
  intro q hpq
  rcases eq_or_lt_of_le hpq with rfl | hpq
  · exact hp
  · rw [sum_filter_eq_zero_of_forall_ne_zero_le s hpq ha]
    exact hc

end Finset
