/-
Copyright (c) 2026 Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters

/-!
# Numerical bounds for the cyclotomic tower degree

The dyadic factor controls the lower bound for `towerDeg s`. The remaining ternary factor is
logarithmic in the prime-sum cutoff `x` and can be absorbed by a small power of the logarithm
of the larger cutoff. These bounds control the contribution of the tower degree to the
archimedean sizes of cyclotomic differents.

## References

* `New.Data.f_mem_Icc` in `grh/src/New/Reduction/Data/Sizes.lean` of lsernau/grh-lean,
  commit `72fead102f663d5c7a407964a13dc0cf9d977207` (the tower-size estimates).
-/

public section

namespace TauCeti.OneSidedBound

/-- The tower degree is at least its dyadic factor. -/
theorem two_pow_le_towerDeg (s : ℕ) : 2 ^ s ≤ towerDeg s := by
  rw [towerDeg_def]
  exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (by decide) (by simp [l₀_def]))

private theorem l₀_le_mul_of_two_pow_le {s : ℕ} {x t : ℝ}
    (hdyadic : (2 : ℝ) ^ s ≤ (4 * x) ^ (11 : ℕ)) (ht : 1 ≤ t) (hxt : Real.log x ≤ t) :
    (l₀ s : ℝ) ≤ 81 * (44 * t) := by
  by_cases hs : s = 0
  · subst s
    norm_num [l₀_def]
    linarith
  have hodd : Odd (11 : ℕ) := by decide
  have htwo : 0 < (2 : ℝ) ^ s := by positivity
  have hx : 0 < x := by linarith [hodd.pow_pos_iff.mp (htwo.trans_le hdyadic)]
  have hlog₄ : Real.log 4 = 2 * Real.log 2 := by
    calc
      Real.log 4 = Real.log ((2 : ℝ) ^ (2 : ℕ)) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have hslog := Real.log_le_log htwo hdyadic
  rw [Real.log_pow, Real.log_pow, Real.log_mul (by norm_num) hx.ne', hlog₄] at hslog
  norm_num at hslog
  have hlog₂ : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hst : (s : ℝ) ≤ 44 * t := by
    refine le_of_mul_le_mul_right ?_ (by linarith : 0 < Real.log 2)
    nlinarith only [hslog, hxt, mul_le_mul_of_nonneg_right hlog₂ (zero_le_one.trans ht),
      mul_le_mul_of_nonneg_right ht (by linarith : 0 ≤ Real.log 2)]
  have hl : (l₀ s : ℝ) ≤ 81 * (s : ℝ) := by exact_mod_cast l₀_le hs
  exact hl.trans (mul_le_mul_of_nonneg_left hst (by norm_num))

/-- If `2^s ≤ (4x)^11`, `log x ^ 6 ≤ log b` and `log (log b) ≥ 10^7`, then the tower
has degree at most `x^11 (log b)^(1/5)`. No separate bound on `s` is needed. -/
theorem towerDeg_le_pow_mul_log_rpow {s : ℕ} {x b : ℝ}
    (hdyadic : (2 : ℝ) ^ s ≤ (4 * x) ^ (11 : ℕ))
    (hscale : Real.log x ^ (6 : ℕ) ≤ Real.log b)
    (hlog : 10 ^ (7 : ℕ) ≤ Real.log (Real.log b)) :
    (towerDeg s : ℝ) ≤ x ^ (11 : ℕ) * Real.log b ^ (1 / 5 : ℝ) := by
  generalize Real.log b = L at *
  have hL : 1 ≤ L := by
    have hL₀ : 0 ≤ L := (by positivity : 0 ≤ Real.log x ^ (6 : ℕ)).trans hscale
    by_contra! h
    linarith [Real.log_nonpos hL₀ h.le]
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hroot : (L ^ (1 / 6 : ℝ)) ^ (6 : ℕ) = L := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLp.le]
    norm_num
  have hxroot : Real.log x ≤ L ^ (1 / 6 : ℝ) := by
    by_cases hx : 0 ≤ Real.log x
    · exact (pow_le_pow_iff_left₀ hx (by positivity) (by decide)).mp (hroot ▸ hscale)
    · exact (le_of_not_ge hx).trans (by positivity)
  have hternary := l₀_le_mul_of_two_pow_le hdyadic (Real.one_le_rpow hL (by norm_num)) hxroot
  -- The difference between the exponents `1/5` and `1/6` pays for the numerical factors.
  have hconst : (3 * 81 * 44 * 4 ^ (11 : ℕ) : ℝ) ≤ L ^ (1 / 30 : ℝ) := by
    rw [Real.rpow_def_of_pos hLp]
    have hle : (10 ^ (7 : ℕ) / 30 : ℝ) ≤ Real.log L * (1 / 30 : ℝ) := by linarith
    refine le_trans ?_ (Real.exp_le_exp.mpr hle)
    exact (by norm_num : (3 * 81 * 44 * 4 ^ (11 : ℕ) : ℝ) ≤
      1 + (10 ^ (7 : ℕ) / 30) + (10 ^ (7 : ℕ) / 30) ^ 2 / 2).trans
      (Real.quadratic_le_exp_of_nonneg (by positivity))
  have hpow : (4 * x) ^ (11 : ℕ) = 4 ^ (11 : ℕ) * x ^ (11 : ℕ) := mul_pow ..
  have hxpow : 0 ≤ x ^ (11 : ℕ) := by
    rw [hpow] at hdyadic
    exact nonneg_of_mul_nonneg_right ((by positivity : 0 ≤ (2 : ℝ) ^ s).trans hdyadic)
      (by positivity)
  push_cast [towerDeg_def]
  calc
    3 * ↑(l₀ s) * (2 : ℝ) ^ s ≤ (3 * (81 * (44 * L ^ (1 / 6 : ℝ)))) * (4 * x) ^ (11 : ℕ) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hternary (by norm_num)) hdyadic
        (by positivity) (by positivity)
    _ = x ^ (11 : ℕ) * ((3 * 81 * 44 * 4 ^ (11 : ℕ)) * L ^ (1 / 6 : ℝ)) := by
      rw [hpow]
      ring
    _ ≤ x ^ (11 : ℕ) * (L ^ (1 / 30 : ℝ) * L ^ (1 / 6 : ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hconst (by positivity)) hxpow
    _ = x ^ (11 : ℕ) * L ^ (1 / 5 : ℝ) := by rw [← Real.rpow_add hLp]; norm_num

end TauCeti.OneSidedBound
