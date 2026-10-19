/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Basic

import Mathlib.Tactic.SplitIfs

/-!
# Carries in addition modulo a natural number

This file records identities for carries in addition modulo a natural number, under
reassociation and under multiplication between two moduli.

## Main results

* `TauCeti.Nat.carry_add_carry`: the two ways to associate a three-term sum produce the same
  total number of carries.
* `Nat.mul_div_add_mul_div_add_carry`: multiplying between moduli scales the carry, up to
  the integer quotients of the scaled summands.
-/

public section

namespace TauCeti.Nat

/-- The carries of `(i + j) + k` and of `i + (j + k)` modulo `n` agree: both count the
multiples of `n` in `i + j + k`. -/
theorem carry_add_carry {n i j k : ℕ} (hi : i < n) (hj : j < n) (hk : k < n) :
    (if n ≤ (i + j) % n + k then 1 else 0) + (if n ≤ i + j then 1 else 0) =
      (if n ≤ j + k then 1 else 0) + (if n ≤ i + (j + k) % n then 1 else 0) := by
  have hmod : ∀ m, m < 2 * n → m % n = if n ≤ m then m - n else m := by
    intro m hm
    split_ifs with h
    · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    · exact Nat.mod_eq_of_lt (by omega)
  rw [hmod (i + j) (by omega), hmod (j + k) (by omega)]
  split_ifs <;> omega

end TauCeti.Nat

namespace Nat

/-- For `i, j < N` and `d N = m n`, the carry after scaling by `d` modulo `n`, together with
the quotients of the scaled summands, equals the scaled carry modulo `N` plus the quotient
of the scaled remainder. -/
theorem mul_div_add_mul_div_add_carry {n N d m i j : ℕ} (hn : 0 < n) (hd : d * N = m * n)
    (hi : i < N) (hj : j < N) :
    d * i / n + d * j / n + (if n ≤ d * i % n + d * j % n then 1 else 0) =
      d * ((i + j) % N) / n + m * (if N ≤ i + j then 1 else 0) := by
  rw [← Nat.add_div hn, ← Nat.mul_add]
  split_ifs with h
  · obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le h
    rw [hr, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega), Nat.mul_one, Nat.mul_add, hd,
      Nat.add_comm (m * n), Nat.add_mul_div_right _ _ hn]
  · rw [Nat.mod_eq_of_lt (by omega), Nat.mul_zero, Nat.add_zero]

end Nat
