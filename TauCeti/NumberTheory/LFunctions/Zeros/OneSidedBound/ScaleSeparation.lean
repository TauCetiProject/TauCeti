/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Scale separation inequalities for admissible one-sided bound data

Admissible data for the one-sided prime sum bound fix three separated scales `x ≤ x₁ ≤ b`
together with a tower exponent `s` bounded by `32 log x`. From the separation inequalities
`x ^ 10 ^ 6 ≤ x₁`, `x₁ ^ 10 ^ 6 ≤ b`, and `(log x₁) ^ 6 ≤ log b`, this file derives three
numerical bounds used across the construction and prime-sum estimates:

## Main results

* `TauCeti.OneSidedBound.secondCutoff_pow_le_sqrt_weightScale`: `x₁ ^ (3 * l₀ s ^ 2) ≤ √b`.
* `TauCeti.OneSidedBound.offWeight_mem_Icc`: `x ^ 999 ≤ x * b / x₁ ≤ b / x ^ 999`.
* `TauCeti.OneSidedBound.Parameters.q₂_le_rpow`: `P.q₂ s ≤ x ^ (33 * (P.q₀ * P.d))`.

## Provenance

Adapted from `New.Data.x₁_pow_le_sqrt_b` and `New.Data.q₂_le` in
`grh/src/New/Reduction/Data/Sizes.lean` and `New.Data.a_div_x₁_mem_Icc` in
`grh/src/New/Reduction/Data/Magnitudes.lean` of `grh-lean`
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC) at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open Real Set

namespace TauCeti.OneSidedBound

/-- For a nonzero tower exponent `s ≤ 32 log x₁` with `(log x₁) ^ 6 ≤ log b` and `343 ≤ log x₁`,
the second cutoff satisfies `x₁ ^ (3 * l₀ s ^ 2) ≤ √b`. -/
theorem secondCutoff_pow_le_sqrt_weightScale {s : ℕ} {x₁ b : ℝ} (hs : s ≠ 0)
    (hx₁ : 1 ≤ x₁) (hb : 0 < b) (hsle : (s : ℝ) ≤ 32 * log x₁)
    (hlog : (log x₁) ^ 6 ≤ log b) (hL : 343 ≤ log x₁) :
    x₁ ^ (3 * l₀ s ^ 2) ≤ √b := by
  have hx₁pos : 0 < x₁ := zero_lt_one.trans_le hx₁
  have hl₀ : (l₀ s : ℝ) ≤ 81 * s := by exact_mod_cast l₀_le hs
  have hbound : 3 * (l₀ s : ℝ) ^ 2 * log x₁ ≤ log b / 2 := by
    have h1 : (l₀ s : ℝ) ≤ 2592 * log x₁ := hl₀.trans (by linarith)
    have h2 : 3 * (l₀ s : ℝ) ^ 2 * log x₁ ≤ 20155392 * (log x₁) ^ 3 := by
      have hsq : (l₀ s : ℝ) ^ 2 ≤ (2592 * log x₁) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) h1 2
      nlinarith
    have h3 : (343 : ℝ) ^ 3 ≤ (log x₁) ^ 3 := pow_le_pow_left₀ (by norm_num) hL 3
    have h4 : 40310784 * (log x₁) ^ 3 ≤ (log x₁) ^ 6 := by
      have : (log x₁) ^ 6 = (log x₁) ^ 3 * (log x₁) ^ 3 := by ring
      nlinarith
    linarith
  rw [← exp_log hx₁pos, ← exp_natCast_mul, sqrt_eq_rpow, ← exp_log hb, ← exp_mul, exp_le_exp]
  simpa [Nat.cast_mul, Nat.cast_pow, mul_div_assoc, div_eq_mul_inv, mul_comm] using hbound

/-- Under the scale separation `x ^ 10 ^ 6 ≤ x₁` and `x₁ ^ 10 ^ 6 ≤ b` with `1 ≤ x`, the
off-place weight `x * b / x₁` lies in `[x ^ 999, b / x ^ 999]`. -/
theorem offWeight_mem_Icc {x x₁ b : ℝ} (hx : 1 ≤ x)
    (hx₁ : x ^ (10 ^ 6) ≤ x₁) (hb : x₁ ^ (10 ^ 6) ≤ b) :
    x * b / x₁ ∈ Icc (x ^ 999) (b / x ^ 999) := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hx₁ge : 1 ≤ x₁ := (one_le_pow₀ hx).trans hx₁
  have hx₁pos : 0 < x₁ := zero_lt_one.trans_le hx₁ge
  have hx1000 : x ^ 1000 ≤ x₁ := (pow_le_pow_right₀ hx (by norm_num)).trans hx₁
  have hx998 : x ^ 998 ≤ x₁ := (pow_le_pow_right₀ hx (by norm_num)).trans hx₁
  constructor
  · rw [le_div_iff₀ hx₁pos]
    have hle : x ^ 998 * x₁ ≤ b := calc
      x ^ 998 * x₁ ≤ x₁ * x₁ := by gcongr
      _ = x₁ ^ 2 := by ring
      _ ≤ x₁ ^ (10 ^ 6) := pow_le_pow_right₀ hx₁ge (by norm_num)
      _ ≤ b := hb
    calc
      x ^ 999 * x₁ = x * (x ^ 998 * x₁) := by ring
      _ ≤ x * b := by gcongr
  · rw [div_le_div_iff₀ hx₁pos (pow_pos hxpos _)]
    have hbpos : 0 ≤ b := (pow_nonneg hx₁pos.le _).trans hb
    calc
      x * b * x ^ 999 = b * x ^ 1000 := by ring
      _ ≤ b * x₁ := by gcongr

/-- The auxiliary modulus `P.q₂ s = (P.q₀ * P.d) ^ (s + 6)` is at most `x ^ (33 * (P.q₀ * P.d))`
when `6 ≤ log x` and `s ≤ 32 log x`. -/
theorem Parameters.q₂_le_rpow (P : Parameters) {s : ℕ} {x : ℝ}
    (hx : 1 ≤ x) (hlog : 6 ≤ log x) (hs : (s : ℝ) ≤ 32 * log x) :
    (P.q₂ s : ℝ) ≤ x ^ (33 * (P.q₀ * P.d)) := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hexp : (s : ℝ) + 6 ≤ 33 * log x := by linarith
  have hbase : ((P.q₀ * P.d : ℕ) : ℝ) ≤ exp ((P.q₀ * P.d : ℕ) : ℝ) := by
    linarith [add_one_le_exp ((P.q₀ * P.d : ℕ) : ℝ)]
  calc
    (P.q₂ s : ℝ) = ((P.q₀ * P.d : ℕ) : ℝ) ^ (s + 6) := by rw [P.q₂_def, Nat.cast_pow]
    _ ≤ (exp ((P.q₀ * P.d : ℕ) : ℝ)) ^ (s + 6) := pow_le_pow_left₀ (Nat.cast_nonneg _) hbase _
    _ = exp (((s : ℝ) + 6) * ((P.q₀ * P.d : ℕ) : ℝ)) := by
      rw [← exp_natCast_mul, Nat.cast_add, Nat.cast_ofNat]
    _ ≤ exp (33 * log x * ((P.q₀ * P.d : ℕ) : ℝ)) := by gcongr
    _ = (exp (log x)) ^ (33 * (P.q₀ * P.d)) := by
      rw [← exp_natCast_mul]; congr 1; push_cast; ring
    _ = x ^ (33 * (P.q₀ * P.d)) := by rw [exp_log hxpos]

end TauCeti.OneSidedBound
