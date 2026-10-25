/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.SuccPred.Basic
public import Mathlib.Order.Iterate

/-!
# Comparing iterated successors

In a successor order, `succ^[n] a` is the element `n` steps above `a`. This file compares such
iterates. Without a maximal element, applying the same number of further steps preserves and
reflects the order, and an element at least `n` steps above `a` lies strictly above every
iterate `succ^[m] a` with `m < n`. An element `b ≥ a` that is none of
`a, succ a, …, succ^[n - 1] a` lies at least `n` steps above `a`.

These comparisons measure how far apart two elements of a discrete order are, up to a bound, as in
the Ehrenfeucht–Fraïssé analysis of discrete linear orders.
-/

public section

namespace Order

variable {α : Type*}

section NoMax

variable [Preorder α] [SuccOrder α] [NoMaxOrder α]

/-- If `b` lies at least `n` successor steps above `a`, then fewer than `n` steps above `a` lies
strictly below any number of steps above `b`. -/
theorem succ_iterate_lt_succ_iterate_of_succ_iterate_le {a b : α} {n m : ℕ}
    (h : succ^[n] a ≤ b) (hm : m < n) (k : ℕ) : succ^[m] a < succ^[k] b :=
  ((succ_strictMono.strictMono_iterate_of_lt_map (lt_succ a) hm).trans_le h).trans_le
    (le_succ_iterate k b)

end NoMax

/-- In a linear order without a maximal element, taking `k` further successor steps on both sides
preserves and reflects the order. -/
theorem succ_iterate_add_le_succ_iterate_add_iff [LinearOrder α] [SuccOrder α] [NoMaxOrder α]
    {a b : α} (m n k : ℕ) :
    succ^[m + k] a ≤ succ^[n + k] b ↔ succ^[m] a ≤ succ^[n] b := by
  rw [Nat.add_comm m k, Nat.add_comm n k, Function.iterate_add_apply, Function.iterate_add_apply]
  exact (succ_strictMono.iterate k).le_iff_le

/-- An element `b ≥ a` that is none of `a, succ a, …, succ^[n - 1] a` lies at least `n` successor
steps above `a`. -/
theorem succ_iterate_le_of_forall_ne [PartialOrder α] [SuccOrder α] {a b : α} (hab : a ≤ b)
    {n : ℕ} (hne : ∀ k < n, succ^[k] a ≠ b) : succ^[n] a ≤ b := by
  induction n with
  | zero => exact hab
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact succ_le_of_lt ((ih fun k hk => hne k (by omega)).lt_of_ne (hne n n.lt_succ_self))

end Order
