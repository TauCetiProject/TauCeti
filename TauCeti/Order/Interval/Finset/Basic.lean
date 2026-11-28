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
# Finite interval partitions and cardinalities

Every closed interval `[a, b]` together with the open lower ray `(-∞, a)` covers the closed lower
ray `(-∞, b]`, and the two pieces are disjoint whenever `a ≤ b`. Also records the two-element
successor interval `Icc a (Order.succ a) = {a, Order.succ a}` and cardinality decrease for nested
closed intervals `Icc a₁ b₁ ⊂ Icc a₂ b₂`.

## Main results

* `Finset.Iio_disjoint_Icc`: `Finset.Iio a` and `Finset.Icc b c` are disjoint when `a ≤ b`.
* `Finset.Iio_union_Icc_eq_Iic`: `Finset.Iio a ∪ Finset.Icc a b = Finset.Iic b` when `a ≤ b`.
* `Finset.Icc_self_succ`: `Finset.Icc a (Order.succ a) = {a, Order.succ a}`.
* `Finset.Icc_self_add_one`: `Finset.Icc a (a + 1) = {a, a + 1}` in a `SuccAddOrder`.
* `Finset.card_Icc_lt_card_Icc_left`, `Finset.card_Icc_lt_card_Icc_right`: moving either endpoint
  strictly inwards on a nonempty closed interval strictly decreases its cardinality.
-/

public section

namespace Finset

variable {α : Type*}

section Preorder

variable [Preorder α] [LocallyFiniteOrder α]

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α] {a b c : α}

/-- `Iio a` and `Icc b c` are disjoint whenever `a ≤ b`. -/
theorem Iio_disjoint_Icc (h : a ≤ b) : Disjoint (Iio a) (Icc b c) :=
  disjoint_left.2 fun _ hxa hbcx ↦ (mem_Iio.1 hxa).not_ge <| h.trans (mem_Icc.1 hbcx).1

end LocallyFiniteOrderBot

variable {a₁ a₂ b₁ b₂ : α}

/-- If `[a₂, b₂]` is nonempty (`a₂ ≤ b₂`) and `[a₁, b₁]` is obtained from it by moving the left
endpoint strictly inwards (`a₂ < a₁`) and the right endpoint not outwards (`b₁ ≤ b₂`), then
`[a₁, b₁]` has strictly fewer elements than `[a₂, b₂]`. This is the cardinality form of
`Finset.Icc_ssubset_Icc_left`. -/
@[to_dual (rename := a₁ ↔ b₁, a₂ ↔ b₂, ha ↔ hb) (reorder := ha hb) card_Icc_lt_card_Icc_right
/-- If `[a₂, b₂]` is nonempty (`a₂ ≤ b₂`) and `[a₁, b₁]` is obtained from it by moving the left
endpoint not outwards (`a₂ ≤ a₁`) and the right endpoint strictly inwards (`b₁ < b₂`), then
`[a₁, b₁]` has strictly fewer elements than `[a₂, b₂]`. This is the cardinality form of
`Finset.Icc_ssubset_Icc_right`. -/]
theorem card_Icc_lt_card_Icc_left (hI : a₂ ≤ b₂) (ha : a₂ < a₁) (hb : b₁ ≤ b₂) :
    #(Icc a₁ b₁) < #(Icc a₂ b₂) :=
  card_lt_card (Icc_ssubset_Icc_left hI ha hb)

end Preorder

section LinearOrder

variable [LinearOrder α] [LocallyFiniteOrder α]

section LocallyFiniteOrderBot

variable [LocallyFiniteOrderBot α] {a b : α}

/-- The union of `Iio a` and `Icc a b` is `Iic b` whenever `a ≤ b`. -/
theorem Iio_union_Icc_eq_Iic (h : a ≤ b) : Iio a ∪ Icc a b = Iic b :=
  coe_injective <| by simpa using Set.Iio_union_Icc_eq_Iic h

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
