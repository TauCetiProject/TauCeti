/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Products of `p` against products of `p - 1` over a finite set of naturals

For a finite set `s` of natural numbers that are all at least `2`, the quotient
`∏_{p ∈ s} p / (p - 1)` is at most `#s + 1`: the `k`-th smallest element of `s` is at least
`k + 1`, so its factor is at most `(k + 1) / k`, and these factors telescope. The statement is
kept in `ℕ`, without division.

## Main results

* `TauCeti.prod_le_prod_sub_one_mul_card_add_one`: for a finite set `s` of naturals `≥ 2`,
  `∏_{p ∈ s} p ≤ (∏_{p ∈ s} (p - 1)) (#s + 1)`.
-/

public section

namespace TauCeti

/-- For a finite set `s` of natural numbers that are all at least `2`,
`∏_{p ∈ s} p ≤ (∏_{p ∈ s} (p - 1)) * (#s + 1)`. Equivalently `∏_{p ∈ s} p / (p - 1) ≤ #s + 1`:
the `k`-th smallest element of `s` is at least `k + 1`, so its factor is at most
`(k + 1) / k`, and these factors telescope. -/
theorem prod_le_prod_sub_one_mul_card_add_one {s : Finset ℕ} (hs : ∀ p ∈ s, 2 ≤ p) :
    ∏ p ∈ s, p ≤ (∏ p ∈ s, (p - 1)) * (s.card + 1) := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have has : a ∉ s := fun h => (hlt a h).false
    have ih := ih fun p hp => hs p (Finset.mem_insert_of_mem hp)
    -- The elements of `s` lie in `[2, a)`, so `#s + 2 ≤ a`.
    have hcard : s.card + 2 ≤ a := by
      have hsub : s ⊆ Finset.Ico 2 a := fun p hp =>
        Finset.mem_Ico.2 ⟨hs p (Finset.mem_insert_of_mem hp), hlt p hp⟩
      have := Finset.card_le_card hsub
      rw [Nat.card_Ico] at this
      have := hs a (Finset.mem_insert_self a s)
      omega
    have key : a * (s.card + 1) ≤ (a - 1) * (s.card + 1 + 1) := by
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      rw [Nat.add_sub_cancel]
      linarith
    rw [Finset.prod_insert has, Finset.prod_insert has, Finset.card_insert_of_notMem has]
    calc a * ∏ p ∈ s, p ≤ a * ((∏ p ∈ s, (p - 1)) * (s.card + 1)) := Nat.mul_le_mul_left a ih
      _ = (∏ p ∈ s, (p - 1)) * (a * (s.card + 1)) := by ring
      _ ≤ (∏ p ∈ s, (p - 1)) * ((a - 1) * (s.card + 1 + 1)) := Nat.mul_le_mul_left _ key
      _ = (a - 1) * (∏ p ∈ s, (p - 1)) * (s.card + 1 + 1) := by ring

end TauCeti
