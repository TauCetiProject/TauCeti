/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Tactic.LinearCombination

/-!
# Uniqueness of signed base-`b` digits

An integer combination `∑ k, c k * b ^ k` of the powers of `b` whose digits all satisfy
`|c k| < b` vanishes only if every digit vanishes. Equivalently, two integers written in base `b`
with digits whose differences are below `b` in absolute value agree only if the digits agree.
Mathlib's `Nat.ofDigits_inj_of_len_eq` is the version for natural digits in `[0, b)`.

## Main results

* `Int.eq_zero_of_sum_mul_pow_eq_zero`: if `∑ k, c k * b ^ k = 0` and every `|c k| < b`, then
  `c = 0`.
-/

public section

open Finset

namespace Int

/-- Signed base-`b` digits are unique: if `∑ k, c k * b ^ k = 0` and every digit satisfies
`|c k| < b`, then every digit vanishes. -/
theorem eq_zero_of_sum_mul_pow_eq_zero {n : ℕ} {b : ℤ} {c : Fin n → ℤ} (hc : ∀ k, |c k| < b)
    (h : ∑ k, c k * b ^ (k : ℕ) = 0) : c = 0 := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    have hsum : c 0 + (∑ k : Fin n, c k.succ * b ^ (k : ℕ)) * b = 0 := by
      simpa [Fin.sum_univ_succ, pow_succ, sum_mul, mul_assoc] using h
    have h0 : c 0 = 0 :=
      eq_zero_of_abs_lt_dvd ⟨-∑ k : Fin n, c k.succ * b ^ (k : ℕ), by linear_combination hsum⟩
        (hc 0)
    have hb : b ≠ 0 := ((abs_nonneg _).trans_lt (hc 0)).ne'
    rw [h0, zero_add, mul_eq_zero, or_iff_left hb] at hsum
    have hs : c ∘ Fin.succ = 0 := ih (fun k => hc k.succ) hsum
    ext k
    exact Fin.cases h0 (fun k => congrFun hs k) k

end Int
