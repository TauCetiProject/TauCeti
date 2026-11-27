/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Rank bounds for chains of theta lifts

Let `m` be the chain length and `r` the rank of the target forms' Hermitian space. The definite
chain starts at rank `r + 1 - m` and adds `5 * r + 1` at each step. The bounds below separate
its initial rank from the chain length, control the final definite rank and the weight gap, and
compare the tower exponent with the logarithmic scale of the second prime-sum cutoff. They depend
only on numerical rank and scale inequalities, not on the cyclotomic field or the prime levels.

For a dyadic chain length `m = 2^e` with `e ≠ 0` and a ternary target rank `r = 3^j`, the initial
rank is even, as needed for indexing the derivative rows. When `r ≥ 2`, the half-gap is at least
the initial rank plus one rank increment. At the dyadic chain length, `m^594 ≤ 2 ^ l₀ (22 * e)`.

The normalization and constants are those of `New.Data` in `New/Reduction/Data/Magnitudes.lean`
and `New/Reduction/Data/Sizes.lean` in the `grh` folder of
<https://github.com/lsernau/grh-lean> at commit `72fead1`.
-/

public section

namespace TauCeti.OneSidedBound

/-- A chain whose length is at least `√x` has length at least `10⁴` when `x ≥ 10⁸`. -/
theorem ten_thousand_le_chainLength {x m : ℕ} (hx : 10 ^ 8 ≤ x) (hm : x ≤ m ^ 2) :
    10 ^ 4 ≤ m := by
  apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (Nat.zero_le m)
  calc
    (10 ^ 4 : ℕ) ^ 2 = 10 ^ 8 := by norm_num
    _ ≤ m ^ 2 := hx.trans hm

/-- The initial rank is at least one hundred times the chain length. -/
theorem hundred_mul_chainLength_le_sourceRank {x m r : ℕ} (hx : 4 ≤ x)
    (hm : m ^ 2 ≤ 4 * x) (hr : x ^ 5 ≤ r) : 100 * m ≤ r + 1 - m := by
  have hmx : m ≤ 2 * x := by
    apply le_of_pow_le_pow_left₀ (n := 2) (by decide) (Nat.zero_le _)
    have hx2 : x ≤ x ^ 2 := le_self_pow₀ (by omega) (by decide)
    calc
      m ^ 2 ≤ 4 * x := hm
      _ ≤ 4 * x ^ 2 := by gcongr
      _ = (2 * x) ^ 2 := by ring
  have hxr : 256 * x ≤ r := calc
    256 * x = 4 ^ 4 * x := by norm_num
    _ ≤ x ^ 4 * x := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hx _)
    _ = x ^ 5 := by ring
    _ ≤ r := hr
  omega

/-- The dyadic chain length and ternary target rank give an even initial rank. -/
theorem even_sourceRank_of_pow {e j : ℕ} (he : e ≠ 0) :
    Even ((3 : ℕ) ^ j + 1 - 2 ^ e) :=
  ((by decide : Odd (3 : ℕ)).pow.add_odd (by decide : Odd (1 : ℕ))).tsub
    ((by decide : Even (2 : ℕ)).pow_of_ne_zero he)

/-- The initial rank is at least `exp(-2) * x^5` under the rank separation inequality. -/
theorem exp_neg_two_mul_le_sourceRank {x m r : ℕ} (hr : x ^ 5 ≤ r)
    (hm : 2 * m ≤ r + 2) :
    Real.exp (-2) * (x : ℝ) ^ 5 ≤ ((r + 1 - m : ℕ) : ℝ) := by
  have hexp : Real.exp (-2) ≤ 1 / 2 := by
    have ht : (2 : ℝ) ≤ Real.exp 2 :=
      Real.exp_one_gt_two.le.trans (Real.exp_le_exp.mpr (by norm_num))
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) ht
  have hk : r ≤ 2 * (r + 1 - m) := by omega
  have hk' : (x : ℝ) ^ 5 ≤ 2 * ((r + 1 - m : ℕ) : ℝ) := by exact_mod_cast hr.trans hk
  calc
    Real.exp (-2) * (x : ℝ) ^ 5 ≤ (1 / 2) * (x : ℝ) ^ 5 := by gcongr
    _ ≤ ((r + 1 - m : ℕ) : ℝ) := by linarith

/-- The row step `5r` is bounded by `exp(8) * x^5` when `r ≤ 3x^5`. -/
theorem rowStep_le_exp_mul {x r : ℕ} (hr : r ≤ 3 * x ^ 5) :
    (5 * r : ℝ) ≤ Real.exp 8 * (x : ℝ) ^ 5 := by
  have hr' : (r : ℝ) ≤ 3 * (x : ℝ) ^ 5 := by exact_mod_cast hr
  calc
    (5 * r : ℝ) ≤ 15 * (x : ℝ) ^ 5 := by linarith
    _ ≤ Real.exp 8 * (x : ℝ) ^ 5 := by
      gcongr
      exact le_trans (by norm_num) (Real.one_add_div_pow_le_exp (m := 8) (by norm_num))

/-- The half-gap in the derivative orders is at least one row increment plus the initial rank. -/
theorem sourceRank_add_rowStep_add_one_le_halfGap {m r : ℕ} (hr : 2 ≤ r) :
    r + 1 - m + 5 * r + 1 ≤ r ^ 8 := by
  have h : 128 ≤ r ^ 7 := by
    simpa using Nat.pow_le_pow_left hr 7
  calc
    r + 1 - m + 5 * r + 1 ≤ 128 * r := by omega
    _ ≤ r ^ 7 * r := Nat.mul_le_mul_right _ h
    _ = r ^ 8 := (pow_succ r 7).symm

/-- The full weight gap is at most `exp(27) * x^40` when the target rank is at most `3x^5`. -/
theorem gap_le_exp_mul {x r : ℕ} (hr : r ≤ 3 * x ^ 5) :
    2 * (r : ℝ) ^ 8 ≤ Real.exp 27 * (x : ℝ) ^ 40 := by
  have hr' : (r : ℝ) ≤ 3 * (x : ℝ) ^ 5 := by exact_mod_cast hr
  calc
    2 * (r : ℝ) ^ 8 ≤ 2 * (3 * (x : ℝ) ^ 5) ^ 8 := by gcongr
    _ = (2 * 3 ^ (8 : ℕ)) * (x : ℝ) ^ 40 := by ring
    _ ≤ Real.exp 27 * (x : ℝ) ^ 40 := by
      gcongr
      exact le_trans (by norm_num) (Real.one_add_div_pow_le_exp (m := 27) (by norm_num))

/-- The final definite rank has size `x^(11/2)` up to a factor of `exp(12)` when the chain length is
between `√x` and `2√x` and the target rank is between `x^5` and `3x^5`. -/
theorem lastRank_mem_Icc {x m r : ℕ} (hx : 0 < x) (hm₁ : √(x : ℝ) ≤ m)
    (hm₂ : (m : ℝ) ≤ 2 * √(x : ℝ)) (hr₁ : x ^ 5 ≤ r) (hr₂ : r ≤ 3 * x ^ 5) :
    ((r + 1 - m + m * (5 * r + 1) : ℕ) : ℝ) ∈
      Set.Icc ((x : ℝ) ^ (11 / 2 : ℝ)) (Real.exp 12 * (x : ℝ) ^ (11 / 2 : ℝ)) := by
  have hx' : 0 < (x : ℝ) := by exact_mod_cast hx
  have hm : 0 < m := Nat.cast_pos.mp ((Real.sqrt_pos.2 hx').trans_le hm₁)
  have hr : 0 < r := (Nat.pow_pos hx).trans_le hr₁
  have hr₁' : (x : ℝ) ^ 5 ≤ r := by exact_mod_cast hr₁
  have hr₂' : (r : ℝ) ≤ 3 * (x : ℝ) ^ 5 := by exact_mod_cast hr₂
  have hpow : (x : ℝ) ^ (11 / 2 : ℝ) = √(x : ℝ) * (x : ℝ) ^ 5 := by
    have hexponent : (11 / 2 : ℝ) = 1 / 2 + (5 : ℕ) := by norm_num
    rw [hexponent, Real.rpow_add hx', ← Real.sqrt_eq_rpow, Real.rpow_natCast]
  rw [Set.mem_Icc, hpow]
  constructor
  · have hmul : m * r ≤ r + 1 - m + m * (5 * r + 1) := by
      exact (Nat.mul_le_mul_left _ (by omega)).trans (Nat.le_add_left _ _)
    exact (mul_le_mul hm₁ hr₁' (by positivity) (by positivity)).trans (by exact_mod_cast hmul)
  · have hmul : r + 1 - m + m * (5 * r + 1) ≤ 7 * m * r := by
      calc
        r + 1 - m + m * (5 * r + 1) ≤ m * r + m * (6 * r) := by
          exact add_le_add ((by omega : r + 1 - m ≤ r).trans (Nat.le_mul_of_pos_left _ hm))
            (Nat.mul_le_mul_left _ (by omega))
        _ = 7 * m * r := by ring
    have h42 : (42 : ℝ) ≤ Real.exp 12 :=
      le_trans (by norm_num) (Real.one_add_div_pow_le_exp (m := 12) (by norm_num))
    calc
      ((r + 1 - m + m * (5 * r + 1) : ℕ) : ℝ) ≤ 7 * m * r := by exact_mod_cast hmul
      _ ≤ 7 * (2 * √(x : ℝ)) * (3 * (x : ℝ) ^ 5) := by gcongr
      _ = 42 * (√(x : ℝ) * (x : ℝ) ^ 5) := by ring
      _ ≤ Real.exp 12 * (√(x : ℝ) * (x : ℝ) ^ 5) := by gcongr

/-- Scale separation converts the logarithmic bound for the tower exponent into a bound by
`log x₁`, where `x₁` is the second cutoff. -/
theorem towerExponent_le_log_cutoff {x x₁ s : ℕ} (hscale : x ^ 1000000 ≤ x₁)
    (hs : (s : ℝ) ≤ 32 * Real.log x) : (s : ℝ) ≤ Real.log x₁ := by
  rcases x.eq_zero_or_pos with rfl | hx
  · simp only [Nat.cast_zero, Real.log_zero, mul_zero] at hs
    exact hs.trans (Real.log_natCast_nonneg _)
  have hx' : 0 < (x : ℝ) := by exact_mod_cast hx
  have hs' : (x : ℝ) ^ (1000000 : ℕ) ≤ x₁ := by exact_mod_cast hscale
  calc
    (s : ℝ) ≤ 32 * Real.log x := hs
    _ ≤ 1000000 * Real.log x :=
      mul_le_mul_of_nonneg_right (by norm_num) (Real.log_natCast_nonneg _)
    _ = Real.log ((x : ℝ) ^ (1000000 : ℕ)) := by simp [Real.log_pow]
    _ ≤ Real.log x₁ := Real.log_le_log (pow_pos hx' _) hs'

/-- At chain length `m = 2^e` and tower exponent `s = 22e`, the auxiliary exponent `l₀ s`
gives `m^594 ≤ 2^(l₀ s)`. -/
theorem chainLength_pow_le_two_pow_l₀ (e : ℕ) :
    ((2 : ℕ) ^ e) ^ 594 ≤ 2 ^ l₀ (22 * e) := by
  rw [← pow_mul]
  apply pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ))
  have h := lt_l₀ (22 * e)
  omega

end TauCeti.OneSidedBound
