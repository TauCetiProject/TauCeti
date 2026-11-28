/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ThetaLift.Level
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Size of the level of a theta-lift chain

The logarithmic window used to select the level gives both a lower bound for the level
and an upper bound for its logarithm. The lower bound separates the level from the
principal-level primes and controls errors with a denominator of `N - 1`.

The level estimates correspond to `New.Data.log_N_mem_Icc` and
`New.Data.levelPrime_mem_Ioo` in `grh/src/New/Reduction/Data/LevelAndTwists.lean` and
`grh/src/New/Reduction/Data/Sizes.lean` of [lsernau/grh-lean][short-proof], respectively.

[short-proof]: https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207
-/

public section

open Real Set

namespace TauCeti.ThetaLift

/-- The logarithmic size of the level selected in the window of width `√L` is between
`m * L` and `25 * m * L`, where `m` is the chain length and `L` the logarithm of the scale. -/
theorem log_level_mem_Icc {m : ℕ} {w M D L N : ℝ}
    (hm : 2 ≤ m) (hL : log (2 * π) ≤ L) (hw : w ∈ Icc 0 L)
    (hM : M ∈ Icc (exp (20 * L)) (exp (22 * L))) (hD : D ∈ Icc 1 (exp L))
    (hN : log N ∈ Icc (logLevelMin m w M D L) (logLevelMin m w M D L + √L)) :
    log N ∈ Icc (m * L) (25 * m * L) := by
  have hmin := logLevelMin_mem_Icc hm hL hw hM hD
  have hπ : 1 ≤ log (2 * π) :=
    (le_log_iff_exp_le (by positivity)).2 (by linarith [exp_one_lt_three, pi_gt_three])
  have hL₁ := hπ.trans hL
  have hsqrt : √L ≤ L := sqrt_le_self_iff.mpr (Or.inr hL₁)
  have hm₁ : (1 : ℝ) ≤ m := Nat.one_le_cast.mpr (by omega)
  have hmul : L ≤ m * L := le_mul_of_one_le_left (zero_le_one.trans hL₁) hm₁
  exact ⟨hmin.1.trans hN.1, hN.2.trans (by linarith [hmin.2])⟩

/-- In powers of the integer scale `b`, the level in the logarithmic window lies between
`b ^ m` and `b ^ (25 * m)`. The lower bound in particular supplies `b ^ 101 ≤ N` for
chains of length at least `101`. -/
theorem level_mem_Icc {m b N : ℕ} {w M D : ℝ}
    (hb : log (2 * π) ≤ log b) (hw : w ∈ Icc 0 (log b))
    (hM : M ∈ Icc (exp (20 * log b)) (exp (22 * log b))) (hD : D ∈ Icc 1 (exp (log b)))
    (hN : log N ∈ Icc (logLevelMin m w M D (log b)) (logLevelMin m w M D (log b) + √(log b))) :
    N ∈ Icc (b ^ m) (b ^ (25 * m)) := by
  have hπ : 1 ≤ log (2 * π) :=
    (le_log_iff_exp_le (by positivity)).2 (by linarith [exp_one_lt_three, pi_gt_three])
  have hbLog₁ := hπ.trans hb
  have hbLog := zero_lt_one.trans_le hbLog₁
  -- Chains of length zero or one have an entirely negative logarithmic window.
  have hm : 2 ≤ m := by
    by_contra! h
    have hmNat : m ≤ 1 := by omega
    have hm₁ : (m : ℝ) ≤ 1 := by exact_mod_cast hmNat
    have hMπ : 2 * π ≤ M :=
      ((log_le_iff_le_exp (by positivity)).mp (hb.trans (by linarith))).trans hM.1
    have hscale : 0 ≤ log (M * D / (2 * π)) := by
      apply log_nonneg
      rw [le_div_iff₀ (by positivity)]
      have hM₀ := (exp_pos _).le.trans hM.1
      simpa using hMπ.trans (le_mul_of_one_le_right hM₀ hD.1)
    have hw₁ : m * w ≤ log (b : ℝ) := by
      calc
        _ ≤ (m : ℝ) * log b := mul_le_mul_of_nonneg_left hw.2 (Nat.cast_nonneg _)
        _ ≤ _ := mul_le_of_le_one_left hbLog.le hm₁
    have hupper := hN.2
    rw [logLevelMin_def] at hupper
    linarith [log_natCast_nonneg N, mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hm₁) hscale,
      sqrt_le_self_iff.mpr (Or.inr hbLog₁)]
  have hlog := log_level_mem_Icc hm hb hw hM hD hN
  have hmPos : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hNLog : 0 < log (N : ℝ) := (mul_pos hmPos hbLog).trans_le hlog.1
  have hNPos : (0 : ℝ) < N := by
    rcases Nat.eq_zero_or_pos N with rfl | hp
    · simp at hNLog
    · exact Nat.cast_pos.mpr hp
  have hbPos : (0 : ℝ) < b := by
    rcases Nat.eq_zero_or_pos b with rfl | hp
    · simp at hbLog
    · exact Nat.cast_pos.mpr hp
  have hlo := (log_le_log_iff (pow_pos hbPos m) hNPos).1
    (by simpa only [log_pow] using hlog.1)
  have hhi := (log_le_log_iff hNPos (pow_pos hbPos (25 * m))).1
    (by simpa only [log_pow, Nat.cast_mul, Nat.cast_ofNat] using hlog.2)
  exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩

/-- Every principal-level prime in `[b ^ 10, b ^ 11]` lies strictly between `b ^ 2`
and the chain's level as soon as `b ^ m ≤ N` and `m > 11`. This separation uses only the
size of the three integers, not primality or congruences. -/
theorem auxiliaryPrime_mem_Ioo {b p m N : ℕ} (hb : 1 < b) (hm : 11 < m)
    (hp : p ∈ Icc (b ^ 10) (b ^ 11)) (hN : b ^ m ≤ N) : p ∈ Ioo (b ^ 2) N :=
  ⟨(pow_lt_pow_right₀ hb (by decide : 2 < 10)).trans_le hp.1,
    hp.2.trans_lt ((pow_lt_pow_right₀ hb hm).trans_le hN)⟩

end TauCeti.ThetaLift
