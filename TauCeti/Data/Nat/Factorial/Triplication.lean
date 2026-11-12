/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Triplication of factorials

In a field of characteristic zero, the factorials `(3k)!` and `(3k + 1)!` factor through
Pochhammer symbols at thirds:

`(3k)! = 27^k k! (⅓)_k (⅔)_k`, `(3k + 1)! = 27^k k! (⅔)_k (4/3)_k`.

These are the factorial forms of Gauss's multiplication formula for `Γ` at `n = 3`, and they turn
Gamma-denominator power series in `z³` into hypergeometric form.

## Main results

* `TauCeti.factorial_three_mul`: `(3k)! = 27^k k! (⅓)_k (⅔)_k`.
* `TauCeti.factorial_three_mul_add_one`: `(3k + 1)! = 27^k k! (⅔)_k (4/3)_k`.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/Airy/Basic/Maclaurin.lean`.
-/

public section

open Polynomial
open scoped Nat

namespace TauCeti

variable {K : Type*} [Field K] [CharZero K]

/-- Triplication of factorials: `(3k)! = 27^k k! (⅓)_k (⅔)_k`. -/
theorem factorial_three_mul (k : ℕ) :
    (((3 * k)! : ℕ) : K) =
      27 ^ k * k ! * (ascPochhammer K k).eval (1 / 3) * (ascPochhammer K k).eval (2 / 3) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 3 * (k + 1) = 3 * k + 2 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast
    rw [ih, ascPochhammer_succ_eval, ascPochhammer_succ_eval, Nat.factorial_succ]
    push_cast
    ring

/-- Triplication of factorials: `(3k + 1)! = 27^k k! (⅔)_k (4/3)_k`. -/
theorem factorial_three_mul_add_one (k : ℕ) :
    (((3 * k + 1)! : ℕ) : K) =
      27 ^ k * k ! * (ascPochhammer K k).eval (2 / 3) * (ascPochhammer K k).eval (4 / 3) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 3 * (k + 1) + 1 = 3 * k + 1 + 2 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ]
    push_cast
    rw [ih, ascPochhammer_succ_eval, ascPochhammer_succ_eval, Nat.factorial_succ]
    push_cast
    ring

end TauCeti
