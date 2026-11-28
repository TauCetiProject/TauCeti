/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev

import TauCeti.Analysis.SpecialFunctions.Log.Bounds

/-!
# Level bounds for the normalised Poincaré map

A level chosen in a logarithmic window lies above the auxiliary primes. Its logarithm,
together with the log-prime mass up to the second cutoff, fits within the error budget
for rounding the local exponents in the rational normalizing factor.

The window and budget are those of `New.Data.log_N_mem_Icc`, `New.Data.levelPrime_mem_Ioo`
and `New.Data.sum_log_smallNonsplitPrimes_union_le` in lsernau/grh-lean, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`. We use Chebyshev's bound for the small primes,
so the budget applies even before restricting to nonsplit primes.
-/

public section

open Real Set

namespace TauCeti.OneSidedBound

/-- A logarithmic window of width `√L` above a point in `[mL, 24mL]` lies in `[mL, 25mL]`
when `m ≥ 1` and `L ≥ 1`. -/
theorem log_mem_Icc_mul_of_mem_Icc_add_sqrt {m : ℕ} {L A N : ℝ} (hm : 0 < m) (hL : 1 ≤ L)
    (hA : A ∈ Icc (m * L) (24 * m * L)) (hN : log N ∈ Icc A (A + √L)) :
    log N ∈ Icc (m * L) (25 * m * L) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsqrt := (sqrt_le_self_iff (x := L)).2 (Or.inr hL)
  have hmul : L ≤ m * L := le_mul_of_one_le_left (by positivity) hm'
  exact ⟨hA.1.trans hN.1, by linarith [hN.2, hA.2]⟩

/-- A natural number in `[b^10, b^11]` is above `b²` and below any level with
`11 * log b < log N`. In particular, a chain of length `m > 11` supplies this gap when
`m * log b ≤ log N`. -/
theorem mem_Ioo_sq_of_mem_Icc_pow_of_log_lt {b p N : ℕ} (hb : 1 < b)
    (hp : p ∈ Icc (b ^ 10) (b ^ 11)) (hN : 11 * log b < log N) : p ∈ Ioo (b ^ 2) N := by
  have hb' : (1 : ℝ) < b := by exact_mod_cast hb
  have hlog := log_nonneg hb'.le
  have hNpos : 0 < log (N : ℝ) := (mul_nonneg (by norm_num) hlog).trans_lt hN
  have hN' := (log_pos_iff (Nat.cast_nonneg N)).mp hNpos
  have hpow : b ^ 11 < N := by
    exact_mod_cast (pow_lt_iff_lt_log (n := 11) (zero_lt_one.trans hb')
      (zero_lt_one.trans hN')).mpr (by simpa only [Nat.cast_ofNat] using hN)
  exact Icc_subset_Ioo (pow_lt_pow_right₀ hb (by decide : 2 < 10)) hpow hp

/-- At the separated cutoffs, the log-prime mass of the small primes plus the logarithm
of the level fits in the rounding budget `b`. Here `X` is the second cutoff. -/
theorem theta_add_log_le_of_pow_le {X b N : ℝ} {m : ℕ} (hX : 2 ≤ X)
    (hb : X ^ 18 ≤ b) (hm : (m : ℝ) ^ 2 ≤ 4 * X)
    (hN : log N ≤ 30 * m * log b) : Chebyshev.theta X + log N ≤ b := by
  have hX0 : 0 ≤ X := by linarith
  have hb0 : 0 ≤ b := (pow_nonneg hX0 _).trans hb
  have hpow : X ^ 9 ≤ √b := (le_sqrt (pow_nonneg hX0 _) hb0).2 (by simpa [← pow_mul] using hb)
  have hwide : 256 * X ≤ √b := calc
    256 * X = (2 : ℝ) ^ 8 * X := by norm_num
    _ ≤ X ^ 8 * X := by gcongr
    _ = X ^ 9 := by ring
    _ ≤ √b := hpow
  have hm' : (m : ℝ) ≤ 2 * X := by nlinarith [sq_nonneg (X - 1), sq_nonneg ((m : ℝ) - 2 * X)]
  have hlog : log b ≤ 2 * √b := by
    simpa [sqrt_eq_rpow, mul_comm] using (log_le_rpow_div hb0 (by norm_num : (0 : ℝ) < 1 / 2))
  have hlevel : log N ≤ b / 2 := calc
    log N ≤ 30 * m * log b := hN
    _ ≤ 30 * m * (2 * √b) := by gcongr
    _ ≤ 120 * X * √b := by nlinarith [mul_nonneg (sub_nonneg.mpr hm') (sqrt_nonneg b)]
    _ ≤ (√b / 2) * √b := by gcongr; linarith
    _ = b / 2 := by rw [div_mul_eq_mul_div, ← sq, sq_sqrt hb0]
  have hsqrt : √b ≤ b := by
    rw [sqrt_le_self_iff]
    exact Or.inr ((one_le_pow₀ (by linarith : 1 ≤ X)).trans hb)
  have hsmall : Chebyshev.theta X ≤ b / 2 := calc
    Chebyshev.theta X ≤ log 4 * X := Chebyshev.theta_le_log4_mul_x hX0
    _ ≤ 2 * X := mul_le_mul_of_nonneg_right log_four_le_two hX0
    _ ≤ √b / 2 := by linarith
    _ ≤ b / 2 := by gcongr
  linarith

end TauCeti.OneSidedBound
