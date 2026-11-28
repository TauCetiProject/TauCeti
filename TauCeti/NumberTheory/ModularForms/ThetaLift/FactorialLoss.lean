/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Factorization

/-!
# Factorial losses for theta jets

To compensate for losses when comparing a theta jet with its local prime sum, take the
product of `⌈6b/k⌉` consecutive positive integers starting just after `l - ⌈6b/k⌉`
(truncated at zero). This product both accounts for the removed factorial factors and has
large enough valuation at every prime `p ≤ k` to pay for the local error budget.

The interval and the budget follow `New.Data.lossProduct` and
`New.Data.error_le_padicValNat_lossProduct` in `grh/src/New/Derivatives/Sharpness/NearPairs.lean`
of [lsernau/grh-lean](https://github.com/lsernau/grh-lean) at revision `72fead1`.
-/

public section

namespace TauCeti.OneSidedBound

open Nat Real

/-- The number of consecutive factors reserved to absorb valuation losses. -/
noncomputable def lossFactorCount (b k : ℝ) : ℕ := ⌈6 * b / k⌉₊

/-- The length of the loss interval is the natural ceiling of `6b/k`. -/
theorem lossFactorCount_def (b k : ℝ) : lossFactorCount b k = ⌈6 * b / k⌉₊ := (rfl)

/-- The loss product at jet order `l` consists of the consecutive factors after
`l - lossFactorCount b k`, with subtraction truncated at zero. -/
noncomputable def lossProduct (b k : ℝ) (l : ℕ) : ℕ :=
  (l - lossFactorCount b k + 1).ascFactorial (lossFactorCount b k)

/-- The loss product is the rising factorial starting at `l - ⌈6b/k⌉ + 1`. -/
theorem lossProduct_def (b k : ℝ) (l : ℕ) : lossProduct b k l =
    (l - lossFactorCount b k + 1).ascFactorial (lossFactorCount b k) := (rfl)

/-- Below the interval length the loss product starts at `1`, so it is a factorial. -/
@[simp] theorem lossProduct_eq_factorial_of_le {b k : ℝ} {l : ℕ} (hl : l ≤ lossFactorCount b k) :
    lossProduct b k l = (lossFactorCount b k).factorial := by
  rw [lossProduct_def, Nat.sub_eq_zero_of_le hl]
  simp

/-- The loss product never vanishes, including when the interval has length zero. -/
theorem lossProduct_pos (b k : ℝ) (l : ℕ) : 0 < lossProduct b k l := by
  rw [lossProduct_def]
  exact Nat.ascFactorial_pos _ _

/-- The loss product has valuation at least that of the factorial of its length. -/
theorem multiplicity_factorial_lossFactorCount_le (p : ℕ) [Fact p.Prime] (b k : ℝ) (l : ℕ) :
    multiplicity p (lossFactorCount b k).factorial ≤ multiplicity p (lossProduct b k l) := by
  refine (multiplicity_dvd_iff_le (lossProduct_pos b k l).ne').mp
    ((pow_multiplicity_dvd ..).trans ?_)
  rw [lossProduct_def]
  exact Nat.factorial_dvd_ascFactorial _ _

/-- Multiplying by the loss product restores the factorial at the maximum of the jet order
and the interval length. -/
theorem factorial_sub_mul_lossProduct (b k : ℝ) (l : ℕ) :
    (l - lossFactorCount b k).factorial * lossProduct b k l =
      (max l (lossFactorCount b k)).factorial := by
  rw [lossProduct_def, Nat.factorial_mul_ascFactorial, Nat.sub_add_eq_max]

/-- Truncating a jet order by the interval length loses at most the valuation of the loss
product. The statement also applies to orders smaller than the interval length. -/
theorem multiplicity_factorial_le_add_lossProduct (p : ℕ) [Fact p.Prime] (b k : ℝ) (l : ℕ) :
    multiplicity p l.factorial ≤ multiplicity p (l - lossFactorCount b k).factorial +
      multiplicity p (lossProduct b k l) := by
  rw [← Nat.multiplicity_mul (Nat.factorial_ne_zero _) (lossProduct_pos b k l).ne',
    factorial_sub_mul_lossProduct]
  exact (multiplicity_dvd_iff_le (Nat.factorial_ne_zero _)).mp
    ((pow_multiplicity_dvd ..).trans (Nat.factorial_dvd_factorial (le_max_left _ _)))

/-- The loss interval is at least as long as the allowed increase `x ^ 42` in jet order. -/
theorem pow_le_lossFactorCount {x b k : ℝ} (hk0 : 0 < k) (hk : k ≤ 3 * x ^ 5)
    (hb : x ^ 47 ≤ b) : x ^ 42 ≤ (lossFactorCount b k : ℝ) := by
  have hx : 0 < x := (Odd.pow_pos_iff (by decide : Odd 5)).1 (by linarith)
  rw [lossFactorCount_def]
  refine ((le_div_iff₀ hk0).2 ?_).trans (Nat.le_ceil _)
  calc
    _ ≤ x ^ 42 * (3 * x ^ 5) := mul_le_mul_of_nonneg_left hk (by positivity)
    _ = 3 * x ^ 47 := by ring
    _ ≤ 6 * b := by linarith [pow_nonneg hx.le 47]

-- Two shares of size `b / (kp)` pay for the logarithmic error and the jet-order shift.
private theorem fixedLoss_le {x b kp : ℝ} (hx : 2 ≤ x) (hb64 : x ^ 64 ≤ b)
    (hkp0 : 0 < kp) (hkp : kp ≤ 9 * x ^ 10) :
    3 * (log b + 2) + x ^ 42 + 2 ≤ 2 * (b / kp) := by
  have hx0 : 0 < x := by linarith
  have hb0 := (pow_pos hx0 64).trans_le hb64
  have hroot : x ^ 32 ≤ √b := (le_sqrt (by positivity) hb0.le).2 (by rwa [← pow_mul])
  have hlog : 3 * log b ≤ b / kp := by
    have hx22 : (54 : ℝ) ≤ x ^ 22 :=
      (by norm_num : (54 : ℝ) ≤ 2 ^ 22).trans (pow_le_pow_left₀ (by norm_num) hx 22)
    have hroot' : 6 * kp ≤ √b := calc
      _ ≤ 54 * x ^ 10 := by linarith
      _ ≤ x ^ 22 * x ^ 10 := by gcongr
      _ = x ^ 32 := (pow_add x 22 10).symm
      _ ≤ √b := hroot
    have hlog' := log_le_rpow_div hb0.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← sqrt_eq_rpow] at hlog'
    apply (le_div_iff₀ hkp0).2
    nlinarith [mul_le_mul_of_nonneg_right hroot' (sqrt_nonneg b),
      mul_le_mul_of_nonneg_right hlog' hkp0.le, sq_sqrt hb0.le]
  have hdegree : x ^ 42 + 8 ≤ b / kp := by
    have hx42 : (8 : ℝ) ≤ x ^ 42 :=
      (by norm_num : (8 : ℝ) ≤ 2 ^ 42).trans (pow_le_pow_left₀ (by norm_num) hx 42)
    have hx12 : (18 : ℝ) ≤ x ^ 12 :=
      (by norm_num : (18 : ℝ) ≤ 2 ^ 12).trans (pow_le_pow_left₀ (by norm_num) hx 12)
    apply (le_div_iff₀ hkp0).2
    calc
      _ ≤ (2 * x ^ 42) * (9 * x ^ 10) := by gcongr; linarith
      _ = 18 * x ^ 52 := by ring
      _ ≤ x ^ 12 * x ^ 52 := by gcongr
      _ = x ^ 64 := (pow_add x 12 52).symm
      _ ≤ b := hb64
  linarith

-- One share pays for all short-exponent terms evaluated at the smaller weight `xb/x₁`.
private theorem smallWeightLoss_le {s : ℕ} {x x₁ b kp : ℝ} (hx : 2 ≤ x)
    (hx₁ : x ^ 64 ≤ x₁) (hb : 0 ≤ b) (hkp0 : 0 < kp) (hkp : kp ≤ 9 * x ^ 10)
    (hs : (s : ℝ) ≤ 32 * log x) : (l₀ s : ℝ) * (x * b / x₁) ≤ b / kp := by
  have hx0 : 0 < x := by linarith
  have hL : (l₀ s : ℝ) ≤ 2592 * x := by
    rcases eq_or_ne s 0 with rfl | hs0
    · norm_num [l₀_def]; linarith
    · have hL : (l₀ s : ℝ) ≤ 81 * (s : ℝ) := by exact_mod_cast l₀_le hs0
      linarith [log_le_self hx0.le]
  have hx52 : (23328 : ℝ) ≤ x ^ 52 :=
    (by norm_num : (23328 : ℝ) ≤ 2 ^ 52).trans (pow_le_pow_left₀ (by norm_num) hx 52)
  have hpay : (l₀ s : ℝ) * x * kp ≤ x₁ := calc
    _ ≤ 2592 * x * x * (9 * x ^ 10) := by gcongr
    _ = 23328 * x ^ 12 := by ring
    _ ≤ x ^ 52 * x ^ 12 := by gcongr
    _ = x ^ 64 := (pow_add x 52 12).symm
    _ ≤ x₁ := hx₁
  rw [← mul_div_assoc, div_le_div_iff₀ ((pow_pos hx0 64).trans_le hx₁) hkp0]
  have h := mul_le_mul_of_nonneg_right hpay hb
  convert h using 1 <;> ring

/-- The loss budget at a small prime fits in the interval product. Here `x₁` is the second
cutoff, `b` is the large weight, `k` is the initial rank, and `s` is the tower exponent. -/
theorem lossBudget_le_multiplicity_lossProduct {p s : ℕ} [hp : Fact p.Prime]
    {x x₁ b k : ℝ} (hx : 2 ≤ x) (hx₁ : x ^ 64 ≤ x₁) (hb : x₁ ≤ b)
    (hk : k ≤ 3 * x ^ 5) (hpk : (p : ℝ) ≤ k) (hs : (s : ℝ) ≤ 32 * log x) (l : ℕ) :
    3 * (log b + 2) + x ^ 42 + 1 + l₀ s * (x * b / x₁) + 2 * b / (k * p) ≤
      (multiplicity p (lossProduct b k l) : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hb64 := hx₁.trans hb
  have hb0 := (pow_pos hx0 64).trans_le hb64
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.out.pos
  have hk0 := hp0.trans_le hpk
  have hkp0 := mul_pos hk0 hp0
  have hkp : k * p ≤ 9 * x ^ 10 := calc
    k * p ≤ (3 * x ^ 5) * (3 * x ^ 5) := by gcongr; exact hpk.trans hk
    _ = _ := by ring
  have hfixed := fixedLoss_le hx hb64 hkp0 hkp
  have hsmall := smallWeightLoss_le hx hx₁ hb0.le hkp0 hkp hs
  have hfactor := multiplicity_mul_div_factorial (p := p) (lossFactorCount b k)
  have hfloor : (lossFactorCount b k : ℝ) / p ≤ ((lossFactorCount b k / p : ℕ) : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one ((lossFactorCount b k : ℝ) / p)
    rw [Nat.floor_div_eq_div] at h
    exact h.le
  have hceil : 6 * b / k ≤ (lossFactorCount b k : ℝ) := by
    rw [lossFactorCount_def]
    exact Nat.le_ceil _
  -- The multiples of `p` alone give the required valuation; rounding costs at most one.
  have hval : 6 * b / (k * p) ≤ (multiplicity p (lossProduct b k l) : ℝ) + 1 := calc
    _ = (6 * b / k) / p := (div_div ..).symm
    _ ≤ (lossFactorCount b k : ℝ) / p := by gcongr
    _ ≤ _ := hfloor.trans (by
      have h : lossFactorCount b k / p ≤ multiplicity p (lossProduct b k l) := by
        apply le_trans _ (multiplicity_factorial_lossFactorCount_le p b k l)
        rw [← hfactor, multiplicity_factorial_mul]
        omega
      exact_mod_cast (Nat.add_le_add_right h 1))
  rw [mul_div_assoc] at hval
  calc
    _ ≤ 5 * (b / (k * p)) - 1 := by
      rw [mul_div_assoc 2]
      linarith only [hfixed, hsmall]
    _ ≤ _ := by linarith only [hval, div_nonneg hb0.le hkp0.le]

/-- Splitting a jet order into three degrees loses at most `3 (log b + 2)` from its factorial
valuation when the total order is at most `2b`. This holds also at the prime `2`. -/
theorem multiplicity_factorial_add_add_le {p b u v w : ℕ} [hp : Fact p.Prime]
    (h : u + v + w ≤ 2 * b) :
    (multiplicity p (u + v + w).factorial : ℝ) ≤
      multiplicity p u.factorial + multiplicity p v.factorial +
        multiplicity p w.factorial + 3 * (Real.log b + 2) := by
  rcases b.eq_zero_or_pos with rfl | hb
  · have hu : u = 0 := by omega
    have hv : v = 0 := by omega
    have hw : w = 0 := by omega
    norm_num [hu, hv, hw]
  have hsplit (i j : ℕ) : multiplicity p (i + j).factorial ≤
      multiplicity p i.factorial + multiplicity p j.factorial + Nat.log p (i + j) := by
    have hchoose := Nat.factorization_choose_le_log (p := p) (n := i + j) (k := j)
    rw [← Nat.multiplicity_eq_factorization hp.out] at hchoose
    have hc := (Nat.choose_pos (Nat.le_add_left j i)).ne'
    rw [← Nat.add_choose_mul_factorial_mul_factorial i j,
      Nat.multiplicity_mul (Nat.mul_ne_zero hc (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _),
      Nat.multiplicity_mul hc (Nat.factorial_ne_zero _)]
    omega
  have hsplit₃ : multiplicity p (u + v + w).factorial ≤
      multiplicity p u.factorial + multiplicity p v.factorial + multiplicity p w.factorial +
        2 * Nat.log p (2 * b) := by
    have h₁ := Nat.log_mono_right (b := p) (show u + v ≤ 2 * b by omega)
    have h₂ := Nat.log_mono_right (b := p) h
    have huv := hsplit u v
    have huvw := hsplit (u + v) w
    omega
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp.out.two_le
  have hlogp : (2 / 3 : ℝ) < Real.log p :=
    (by linarith [log_two_gt_d9] : (2 / 3 : ℝ) < Real.log 2).trans_le (log_le_log (by norm_num) hp')
  have hℓ := Real.natLog_le_logb (2 * b) p
  rw [Real.logb, le_div_iff₀ (by linarith : 0 < log (p : ℝ))] at hℓ
  push_cast at hℓ
  rw [log_mul (by norm_num) (by positivity)] at hℓ
  have hbound : 2 * (Nat.log p (2 * b) : ℝ) ≤ 3 * (Real.log b + 2) := by
    nlinarith only [hℓ, log_two_lt_d9, mul_le_mul_of_nonneg_left hlogp.le
      (Nat.cast_nonneg (Nat.log p (2 * b)) : (0 : ℝ) ≤ Nat.log p (2 * b))]
  have hreal : (multiplicity p (u + v + w).factorial : ℝ) ≤
      multiplicity p u.factorial + multiplicity p v.factorial + multiplicity p w.factorial +
        2 * (Nat.log p (2 * b) : ℝ) := by exact_mod_cast hsplit₃
  linarith only [hreal, hbound]

end TauCeti.OneSidedBound
