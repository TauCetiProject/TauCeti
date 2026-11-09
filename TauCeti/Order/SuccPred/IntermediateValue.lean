/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.SuccPred.Basic

/-!
# Discrete intermediate values

A sequence in a linearly ordered successor order that increases by at most one successor at
each step attains every value between its initial and final values. Downward jumps and repeated
values are allowed. The step bound is needed only on the finite interval in question.

This separates finite level crossing from the limit argument in
`TauCeti.map_atTop_eq_of_le_add_one`: a sequence tending to infinity with eventually bounded
upward steps takes every sufficiently large natural value.
-/

public section

namespace Nat

/-- **Discrete intermediate value theorem.** If a sequence increases by at most one successor
at each step between `a` and `b`, then it attains every value between `f a` and `f b` at an index
in `[a, b]`. No restriction is imposed on downward jumps. -/
theorem exists_mem_Icc_eq_of_le_succ {α : Type*} [LinearOrder α] [SuccOrder α]
    {f : ℕ → α} {a b : ℕ} {y : α} (hab : a ≤ b)
    (hstep : ∀ i, a ≤ i → i < b → f (i + 1) ≤ Order.succ (f i))
    (ha : f a ≤ y) (hb : y ≤ f b) : ∃ i ∈ Set.Icc a b, f i = y := by
  induction b, hab using Nat.le_induction with
  | base => exact ⟨a, ⟨le_rfl, le_rfl⟩, le_antisymm ha hb⟩
  | succ b hab ih =>
    by_cases hy : y ≤ f b
    · obtain ⟨i, hi, hfi⟩ :=
        ih (fun i hai hib ↦ hstep i hai (hib.trans (Nat.lt_succ_self b))) hy
      exact ⟨i, ⟨hi.1, hi.2.trans (Nat.le_succ b)⟩, hfi⟩
    · exact ⟨b + 1, ⟨hab.trans (Nat.le_succ b), le_rfl⟩,
        le_antisymm ((hstep b hab (Nat.lt_succ_self b)).trans
          (Order.succ_le_of_lt (lt_of_not_ge hy))) hb⟩

end Nat
