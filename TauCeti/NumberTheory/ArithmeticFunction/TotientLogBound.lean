/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Explicit logarithmic lower bound for Euler's totient

An elementary induction on the least element shows that for any finite set `S` of natural
numbers strictly exceeding `a`, the product `∏ p ∈ S, (1 - p⁻¹)` is at least `a / (a + #S)`.
Applying this to the prime factors of `n` together with `2 ^ #n.primeFactors ≤ n` yields the
explicit bound `n ≤ φ n * (2 * Real.log n + 1)` for every natural number `n`.

## Provenance

Adapted from `grh-lean` (<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026
Anthropic, PBC), commit `72fead102f663d5c7a407964a13dc0cf9d977207`, specifically
`New.div_add_card_le_prod_one_sub_inv` and `New.le_totient_mul_log` in
`grh/src/Lib/Analytic/Primes.lean`.
-/

public section

open Finset Real

namespace TauCeti

/-- If every element of a finite set `S` of natural numbers strictly exceeds `a`, then
`a / (a + #S) ≤ ∏ p ∈ S, (1 - p⁻¹)`. -/
theorem div_add_card_le_prod_one_sub_inv (S : Finset ℕ) (a : ℕ) (ha : ∀ p ∈ S, a < p) :
    (a : ℚ) / (a + S.card) ≤ ∏ p ∈ S, (1 - (p : ℚ)⁻¹) := by
  induction S using Finset.induction_on_min generalizing a with
  | empty => simp [div_self_le_one]
  | insert b S hb ih =>
    have hab : (a : ℚ) + 1 ≤ b := by exact_mod_cast ha b (mem_insert_self b S)
    have hnot : b ∉ S := fun h ↦ (hb b h).false
    rw [prod_insert hnot, card_insert_of_notMem hnot]
    refine le_trans ?_
      (mul_le_mul_of_nonneg_left (ih b hb) (sub_nonneg.mpr (Nat.cast_inv_le_one b)))
    rw [Nat.cast_succ, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by linarith)]
    nlinarith [mul_inv_cancel₀ (a := (b : ℚ)) (by linarith)]

/-- Every natural number `n` satisfies `n ≤ φ n * (2 * Real.log n + 1)`. -/
theorem le_totient_mul_two_mul_log_add_one (n : ℕ) :
    (n : ℝ) ≤ Nat.totient n * (2 * Real.log n + 1) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  set j : ℕ := n.primeFactors.card
  have htwo : 2 ^ j ≤ n :=
    (Finset.pow_card_le_prod _ _ 2 fun _ hp ↦ (Nat.prime_of_mem_primeFactors hp).two_le).trans
      (Nat.le_of_dvd hn n.prod_primeFactors_dvd)
  have hcard : (j : ℝ) * Real.log 2 ≤ Real.log n := by
    have hlog := Real.log_le_log (by positivity) (by exact_mod_cast htwo : ((2 : ℝ) ^ j) ≤ n)
    simpa [Real.log_pow] using hlog
  have htot : (n : ℝ) ≤ Nat.totient n * (1 + j) := by
    have hprod : ((1 : ℕ) : ℚ) / ((1 : ℕ) + j) ≤
        ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) :=
      div_add_card_le_prod_one_sub_inv _ 1 fun _ hp ↦ (Nat.prime_of_mem_primeFactors hp).one_lt
    have hrat : (n : ℚ) ≤ Nat.totient n * (1 + j) := by
      rw [Nat.totient_eq_mul_prod_factors, mul_assoc]
      exact le_mul_of_one_le_right (by positivity)
        ((div_le_iff₀ (by positivity)).mp (by simpa using hprod))
    exact_mod_cast hrat
  refine htot.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  nlinarith [Real.log_two_gt_d9]

/-- Every natural number `n` satisfies `n / φ n ≤ 2 * Real.log n + 1`. -/
theorem div_totient_le_two_mul_log_add_one (n : ℕ) :
    (n : ℝ) / Nat.totient n ≤ 2 * Real.log n + 1 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  exact (div_le_iff₀ (Nat.cast_pos.mpr (Nat.totient_pos.mpr hn))).mpr
    (by simpa [mul_comm] using le_totient_mul_two_mul_log_add_one n)

end TauCeti
