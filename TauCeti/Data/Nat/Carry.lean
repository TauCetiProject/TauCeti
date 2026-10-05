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

This file records the elementary identity equating the carries produced by the two associations
of a sum of three natural numbers modulo `n`.

## Main results

* `TauCeti.Nat.carry_add_carry`: the two ways to associate a three-term sum produce the same
  total number of carries.
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
