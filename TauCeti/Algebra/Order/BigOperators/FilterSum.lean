/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Finite sums over ordered filters

This file records elementary consequences of a finite family being zero away from an initial
interval.  They are useful whenever a filtered finite sum is evaluated after all of its nonzero
terms have been passed.
-/

public section

open Set
open scoped BigOperators

namespace TauCeti

variable {ι α M : Type*} [Preorder α] [AddCommMonoid M]

/-- A nonzero term whose index is at or to the left of `p` does not occur strictly between `p` and
any later point. -/
theorem not_mem_Ioo_of_ne_zero_of_forall_le {a : ι → α} {e : ι → M} {p q : α}
    (ha : ∀ i, e i ≠ 0 → a i ≤ p) :
    ∀ i, e i ≠ 0 → a i ∉ Ioo p q := by
  intro i hei hi
  exact (not_lt_of_ge (ha i hei)) hi.1

/-- If all nonzero terms of a finite family have indices at or to the left of `p`, then its sum
over the terms indexed by `q` vanishes whenever `p < q`. -/
theorem filter_sum_eq_zero_of_forall_ne_zero_le [DecidableEq α] (s : Finset ι) {a : ι → α}
    {e : ι → M} {p q : α} (hpq : p < q) (ha : ∀ i, e i ≠ 0 → a i ≤ p) :
    Finset.sum (s.filter (fun i => a i = q)) e = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  by_contra hei
  have hai := ha i hei
  exact (not_lt_of_ge hai) ((Finset.mem_filter.mp hi).2 ▸ hpq)

end TauCeti
