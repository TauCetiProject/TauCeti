/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Order.Interval.Finset.SuccPred

/-!
# Finite interval partitions at an interior point

Every closed interval `[a, b]` together with the open lower ray `(-∞, a)` covers the closed lower
ray `(-∞, b]`, and the two pieces are disjoint whenever `a ≤ b`. Also records the two-element
successor interval `Icc a (Order.succ a) = {a, Order.succ a}`.

## Main results

* `Finset.Iio_disjoint_Icc`: `Finset.Iio a` and `Finset.Icc b c` are disjoint when `a ≤ b`.
* `Finset.Iio_union_Icc_eq_Iic`: `Finset.Iio a ∪ Finset.Icc a b = Finset.Iic b` when `a ≤ b`.
* `Finset.Icc_self_succ`: `Finset.Icc a (Order.succ a) = {a, Order.succ a}`.
* `Finset.Icc_self_add_one`: `Finset.Icc a (a + 1) = {a, a + 1}` in a `SuccAddOrder`.
-/

public section

namespace Finset

variable {α : Type*}

section Preorder

variable [Preorder α] [LocallyFiniteOrder α] [LocallyFiniteOrderBot α] {a b c : α}

/-- `Iio a` and `Icc b c` are disjoint whenever `a ≤ b`. -/
theorem Iio_disjoint_Icc (h : a ≤ b) : Disjoint (Iio a) (Icc b c) :=
  disjoint_left.2 fun _ hxa hbcx ↦ (mem_Iio.1 hxa).not_ge <| h.trans (mem_Icc.1 hbcx).1

end Preorder

section LinearOrder

variable [LinearOrder α] [LocallyFiniteOrder α]

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α] {a b : α}

/-- The union of `Iio a` and `Icc a b` is `Iic b` whenever `a ≤ b`. -/
theorem Iio_union_Icc_eq_Iic (h : a ≤ b) : Iio a ∪ Icc a b = Iic b := by
  ext x
  simp only [mem_union, mem_Iio, mem_Icc, mem_Iic]
  exact ⟨fun hx ↦ hx.elim (fun hxa ↦ (le_of_lt hxa).trans h) And.right,
    fun hxb ↦ (lt_or_ge x a).imp_right fun hax ↦ ⟨hax, hxb⟩⟩

end LocallyFiniteOrderBot

section SuccOrder

variable [SuccOrder α]

/-- The closed interval `[a, Order.succ a]` equals `{a, Order.succ a}`. -/
theorem Icc_self_succ (a : α) : Icc a (Order.succ a) = {a, Order.succ a} := by
  rw [← insert_Icc_right_eq_Icc_succ (Order.le_succ a), Icc_self, pair_comm]

end SuccOrder

section SuccAddOrder

/-- The closed interval `[a, a + 1]` equals `{a, a + 1}` in a `SuccAddOrder`. -/
theorem Icc_self_add_one [Add α] [One α] [SuccAddOrder α] (a : α) :
    Icc a (a + 1) = {a, a + 1} := by
  simpa only [Order.succ_eq_add_one] using Icc_self_succ a

end SuccAddOrder

end LinearOrder

end Finset
