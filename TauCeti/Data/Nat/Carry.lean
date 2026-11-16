/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Basic

import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Carries in addition modulo a natural number

This file records identities for carries in addition modulo a natural number, under
reassociation and under multiplication between two moduli.

## Main results

* `Nat.carry_add_carry`: the two ways to associate a three-term sum produce the same total
  number of carries.
* `Nat.add_eq_mod_add_carry`: for `n = m d`, the carry of `m p + m q` modulo `n` is the carry of
  `p + q` modulo `d`.
* `Nat.mul_div_add_mul_div_add_carry`: multiplying between moduli scales the carry, up to
  the integer quotients of the scaled summands.
-/

public section

namespace Nat

/-- The carries of `(i + j) + k` and of `i + (j + k)` modulo `n` agree: both count the
multiples of `n` in `i + j + k`. -/
theorem carry_add_carry {n i j k : ℕ} (hi : i < n) (hj : j < n) (hk : k < n) :
    (if n ≤ (i + j) % n + k then 1 else 0) + (if n ≤ i + j then 1 else 0) =
      (if n ≤ j + k then 1 else 0) + (if n ≤ i + (j + k) % n then 1 else 0) := by
  simp only [add_mod_eq_ite, mod_eq_of_lt hi, mod_eq_of_lt hj, mod_eq_of_lt hk]
  split_ifs <;> omega

/-- **Carries under scaling.** For `n = m d` and `p, q < d`, the carry of
`m p + m q` modulo `n` is the carry of `p + q` modulo `d`. -/
theorem add_eq_mod_add_carry {m d n p q : ℕ} (hmd : m * d = n) (hp : p < d)
    (hq : q < d) :
    m * p + m * q = (m * p + m * q) % n + n * if d ≤ p + q then 1 else 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain rfl : n = 0 := by simpa using hmd.symm
    simp
  have hlt : m * p + m * q < 2 * n := calc
    m * p + m * q = m * (p + q) := (mul_add _ _ _).symm
    _ < m * (2 * d) := Nat.mul_lt_mul_of_pos_left (by omega) hm
    _ = 2 * n := by rw [← hmd]; ring
  have hle (h : d ≤ p + q) : n ≤ m * p + m * q := calc
    n = m * d := hmd.symm
    _ ≤ m * (p + q) := Nat.mul_le_mul_left m h
    _ = m * p + m * q := mul_add _ _ _
  have hlt' (h : p + q < d) : m * p + m * q < n := calc
    m * p + m * q = m * (p + q) := (mul_add _ _ _).symm
    _ < m * d := Nat.mul_lt_mul_of_pos_left h hm
    _ = n := hmd
  generalize m * p + m * q = X at *
  split_ifs with h
  · rw [Nat.mod_eq_sub_mod (hle h), Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (hlt' (not_le.1 h))]
    omega

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
    rw [hr, add_mod_left, mod_eq_of_lt (by omega), Nat.mul_one, Nat.mul_add, hd,
      Nat.add_comm (m * n), add_mul_div_right _ _ hn]
  · rw [mod_eq_of_lt (by omega), Nat.mul_zero, Nat.add_zero]

end Nat
