/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Pochhammer
import TauCeti.Data.Nat.Factorial.NatCast
import Mathlib.Tactic.FieldSimp

/-!
# Triplication of factorials

In any field, the factorials `(3k)!` and `(3k + 1)!` factor through Pochhammer symbols at thirds
(in characteristic three, `1/3 = 0` and both sides vanish for `k ≥ 1`):

`(3k)! = 27^k k! (⅓)_k (⅔)_k`, `(3k + 1)! = 27^k k! (⅔)_k (4/3)_k`.

These are the factorial forms of Gauss's multiplication formula for `Γ` at `n = 3`, and they turn
Gamma-denominator power series in `z³` into hypergeometric form.

## Main results

* `Nat.factorial_three_mul`: `(3k)! = 27^k k! (⅓)_k (⅔)_k`.
* `Nat.factorial_three_mul_add_one`: `(3k + 1)! = 27^k k! (⅔)_k (4/3)_k`.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/Airy/Basic/Maclaurin.lean`.
-/

public section

open Polynomial
open scoped Nat

namespace Nat

variable {K : Type*} [Field K]

/-- Triplication of factorials: `(3k)! = 27^k k! (⅓)_k (⅔)_k`. -/
theorem factorial_three_mul (k : ℕ) :
    (((3 * k)! : ℕ) : K) =
      27 ^ k * k ! * (ascPochhammer K k).eval (1 / 3) * (ascPochhammer K k).eval (2 / 3) := by
  rcases eq_or_ne (3 : K) 0 with h3 | h3
  · -- If `3 = 0`, then `1/3 = 2/3 = 0`, and both sides vanish for `k ≥ 1`.
    cases k with
    | zero => simp
    | succ k =>
      simp [cast_factorial_eq_zero_of_le (m := 3) (by norm_num) (by exact_mod_cast h3)
        (by omega : 3 ≤ 3 * (k + 1)), h3]
  · induction k with
    | zero => simp
    | succ k ih =>
      have h : 3 * (k + 1) = 3 * k + 2 + 1 := by ring
      rw [h, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      rw [ih, ascPochhammer_succ_eval, ascPochhammer_succ_eval, Nat.factorial_succ]
      push_cast
      field_simp
      ring

/-- Triplication of factorials: `(3k + 1)! = 27^k k! (⅔)_k (4/3)_k`. -/
theorem factorial_three_mul_add_one (k : ℕ) :
    (((3 * k + 1)! : ℕ) : K) =
      27 ^ k * k ! * (ascPochhammer K k).eval (2 / 3) * (ascPochhammer K k).eval (4 / 3) := by
  rcases eq_or_ne (3 : K) 0 with h3 | h3
  · cases k with
    | zero => simp
    | succ k =>
      simp [cast_factorial_eq_zero_of_le (m := 3) (by norm_num) (by exact_mod_cast h3)
        (by omega : 3 ≤ 3 * (k + 1) + 1), h3]
  · induction k with
    | zero => simp
    | succ k ih =>
      have h : 3 * (k + 1) + 1 = 3 * k + 1 + 2 + 1 := by ring
      rw [h, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      rw [ih, ascPochhammer_succ_eval, ascPochhammer_succ_eval, Nat.factorial_succ]
      push_cast
      field_simp
      ring

end Nat
