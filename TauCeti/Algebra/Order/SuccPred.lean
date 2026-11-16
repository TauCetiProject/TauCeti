/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.OrderIso
public import Mathlib.Order.SuccPred.Basic

/-!
# Successors in ordered additive groups

In an ordered additive group the translations `x ↦ a + x` are order isomorphisms, so they commute
with the successor function: `a + succ b = succ (a + b)`. In particular `succ a = a + succ 0`, so
the successor function of a discretely ordered abelian group is translation by its least positive
element `succ 0`. Unlike Mathlib's `SuccAddOrder`, this does not ask the instance `One` to be that
element: on `Lex (Fin n → ℤ)` the instance `One` is the constant function `1`, which is not the
least positive element when `n ≥ 2`.

This file also records basic facts about the finite positive multiples `(k + 1) • succ 0` of
`succ 0`: any positive element avoiding them up to `n` lies strictly above `n • succ 0`
(`TauCeti.Order.nsmul_succ_zero_lt_of_forall_ne`), every positive element `≤ n • succ 0` is one of
them (`TauCeti.Order.exists_eq_succ_nsmul_of_pos_le_nsmul`), and membership in this set is
invariant under `succ` on nonzero elements (`TauCeti.Order.exists_succ_eq_succ_nsmul_iff`).
-/

public section

namespace TauCeti.Order

open _root_.Order

variable {α : Type*} [AddGroup α] [PartialOrder α] [AddLeftMono α] [SuccOrder α]

/-- Translations commute with the successor function. -/
theorem add_succ (a b : α) : a + succ b = succ (a + b) :=
  (OrderIso.addLeft a).map_succ b

/-- The successor of `a` is `a` plus the least positive element `succ 0`. -/
theorem succ_eq_add_succ_zero (a : α) : succ a = a + succ 0 := by
  rw [add_succ, add_zero]

/-- A positive element `β` that is none of the finite positive multiples `(k + 1) • succ 0` for
`k < n` lies strictly above `n • succ 0`. -/
theorem nsmul_succ_zero_lt_of_forall_ne {β : α} (h0 : 0 < β) (n : ℕ)
    (hne : ∀ k < n, β ≠ (k + 1) • succ 0) : n • succ 0 < β := by
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    rw [succ_nsmul, ← succ_eq_add_succ_zero]
    refine (succ_le_of_lt (ih fun k hk => hne k (Nat.lt_succ_of_lt hk))).lt_of_ne ?_
    rw [succ_eq_add_succ_zero, ← succ_nsmul]
    exact (hne n (Nat.lt_succ_self n)).symm

/-- Every positive element `β ≤ n • succ 0` is a positive finite multiple `(k + 1) • succ 0`
with `k < n`. -/
theorem exists_eq_succ_nsmul_of_pos_le_nsmul {β : α} {n : ℕ} (h0 : 0 < β)
    (hle : β ≤ n • succ 0) : ∃ k < n, β = (k + 1) • succ 0 :=
  Classical.byContradiction fun h =>
    (nsmul_succ_zero_lt_of_forall_ne h0 n fun k hk heq => h ⟨k, hk, heq⟩).not_ge hle

/-- For any nonzero element `β`, `succ β` is a positive finite multiple of `succ 0` iff `β` is. -/
theorem exists_succ_eq_succ_nsmul_iff {β : α} (hβ : β ≠ 0) :
    (∃ n : ℕ, succ β = (n + 1) • succ 0) ↔ ∃ n : ℕ, β = (n + 1) • succ 0 := by
  constructor
  · rintro ⟨n, hn⟩
    rw [succ_eq_add_succ_zero, succ_nsmul, add_left_inj] at hn
    cases n with
    | zero =>
      simp only [zero_nsmul] at hn
      exact (hβ hn).elim
    | succ k => exact ⟨k, hn⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n + 1, by rw [succ_eq_add_succ_zero, ← succ_nsmul]⟩

end TauCeti.Order
