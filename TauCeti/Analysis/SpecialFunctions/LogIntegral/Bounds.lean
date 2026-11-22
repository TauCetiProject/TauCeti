/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.LogIntegral.Unoffset
import Mathlib.Analysis.Complex.ExponentialBounds
import TauCeti.Analysis.SpecialFunctions.Exp.DividedDifference
import TauCeti.Analysis.SpecialFunctions.Integrals.InvLog
import TauCeti.Analysis.SpecialFunctions.Log.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Log.Bounds
import TauCeti.Analysis.SpecialFunctions.Log.Deriv

/-!
# Explicit bounds and asymptotic expansion for the logarithmic integral

These bounds translate between the offset logarithmic integral `TauCeti.Real.logIntegral` (`Li`),
the unoffset logarithmic integral `Real.li`, and explicit `x / log x ^ k` approximations in
prime-counting estimates. Because Mathlib currently supplies only `1 / 2 < γ < 2 / 3` for the
Euler–Mascheroni constant, this file records both the sharp enclosure
`0.4679475 ≤ li 2 - γ ≤ 0.4679495` (which yields tighter `li 2` bounds whenever a sharper enclosure
of `γ` is available) and the resulting unconditional enclosure `0.96 < li 2 < 1.14`.

* **Asymptotic expansion**: repeated integration by parts gives
  `li x - (x / log x) * ∑ k ∈ range n, k! / log x ^ k = O(x / log x ^ (n + 1))` as `x → ∞`,
  together with `li ~ Li ~ x / log x`.
* **Numerical enclosures of `li 2 - γ` and `li 2`**: combining the `y = log 2` series enclosure
  `∑_{n ≥ 1} (log 2)^n / (n * n!) ∈ [0.8344605, 0.8344615]` (from
  `TauCeti.Analysis.SpecialFunctions.Exp.DividedDifference`) with
  `log (log 2) ∈ [-0.366513, -0.366512]` yields `0.4679475 ≤ li 2 - γ ≤ 0.4679495` and
  `0.96 < li 2 < 1.14`.
* **Bounds and unique zero of `Li x - x / log x`**: strict monotonicity on `(1, ∞)`, explicit
  two-sided bounds for `x ≥ 2`, localization of the unique zero in `(6.5797, 6.5798)`, sign bounds
  away from `(6.5797, 6.5798)`, and Fiori–Kadiri–Swidinsky's lower bound
  `(x - 6.58) / log x ^ 2 ≤ Li x - x / log x` for `x ≥ 6.58`.

## Main declarations

* `Real.logIntegral_eq_sum_add_integral`, `Real.isBigO_logIntegral_sub_mul_sum`,
  `Real.isBigO_li_sub_mul_sum`, `Real.li_isEquivalent_logIntegral`,
  `Real.li_isEquivalent_div_log` — asymptotic expansion and prime-number-theorem equivalences for
  `li`.
* `Real.le_li_two_sub_eulerMascheroniConstant`, `Real.li_two_sub_eulerMascheroniConstant_le`,
  `Real.lt_li_two`, `Real.li_two_lt` — enclosures of `li 2 - γ` and `li 2`.
* `Real.strictMonoOn_logIntegral_sub_div_log`, `Real.le_logIntegral_sub_div_log`,
  `Real.lt_logIntegral_sub_div_log`, `Real.logIntegral_sub_div_log_lt`,
  `Real.existsUnique_logIntegral_sub_div_log_eq_zero`,
  `Real.existsUnique_logIntegral_sub_div_log_eq_zero_Ioo`,
  `Real.logIntegral_sub_div_log_neg`, `Real.logIntegral_sub_div_log_pos`,
  `Real.sub_div_log_sq_le_logIntegral_sub_div_log` — monotonicity, bounds, unique zero, and
  Fiori–Kadiri–Swidinsky Lemma 20 for `Li x - x / log x`.

## References

* F. W. J. Olver et al., *NIST Digital Library of Mathematical Functions*, §6.2 and §6.12.
* A. Fiori, H. Kadiri, and J. Swidinsky, *Sharper bounds for the error term in the prime number
  theorem*, *Res. Number Theory* 9 (2023), Article 63, Lemma 20.
-/

public section

open Asymptotics Filter MeasureTheory Set TauCeti.Real
open scoped Topology Nat

namespace Real

/-! ### Asymptotic expansion of `Li` and `li` -/

/-- Exact `n`-fold integration-by-parts expansion of `Li x` for every `n : ℕ` and `x > 1`. -/
theorem logIntegral_eq_sum_add_integral (n : ℕ) {x : ℝ} (hx : 1 < x) :
    logIntegral x =
      (x / log x) * (∑ k ∈ Finset.range n, (k ! : ℝ) / log x ^ k) -
        (2 / log 2) * (∑ k ∈ Finset.range n, (k ! : ℝ) / log 2 ^ k) +
        (n ! : ℝ) * ∫ t in (2 : ℝ)..x, (log t ^ (n + 1))⁻¹ := by
  induction n with
  | zero =>
      simp [logIntegral_def]
  | succ n ih =>
      rw [ih, integral_inv_log_pow_eq_sub_add (n + 1) one_lt_two hx,
        Finset.sum_range_succ, Finset.sum_range_succ, mul_add, mul_add, mul_add,
        Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hterm (y : ℝ) : (y / log y) * ((n ! : ℝ) / log y ^ n) =
          (n ! : ℝ) * (y / log y ^ (n + 1)) := by
        rw [pow_succ']
        ring
      rw [hterm x, hterm 2]
      ring

/-- **Asymptotic expansion of `Li`**: for every `n : ℕ`,
`Li x - (x / log x) * ∑ k ∈ range n, k! / log x ^ k = O(x / log x ^ (n + 1))`. -/
theorem isBigO_logIntegral_sub_mul_sum (n : ℕ) :
    (fun x : ℝ ↦
      logIntegral x - (x / log x) * ∑ k ∈ Finset.range n, (k ! : ℝ) / log x ^ k)
      =O[atTop] fun x : ℝ ↦ x / log x ^ (n + 1) := by
  have hconst := (isLittleO_const_div_log_pow
    (-(2 / log 2) * ∑ k ∈ Finset.range n, (k ! : ℝ) / log 2 ^ k) (n + 1)).isBigO
  have hrem := (isBigO_integral_inv_log_pow (n + 1)).const_mul_left (n ! : ℝ)
  refine (hconst.add hrem).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [logIntegral_eq_sum_add_integral n hx]
  ring

/-- **Asymptotic expansion of `li`**: for every `n : ℕ`,
`li x - (x / log x) * ∑ k ∈ range n, k! / log x ^ k = O(x / log x ^ (n + 1))`. -/
theorem isBigO_li_sub_mul_sum (n : ℕ) :
    (fun x : ℝ ↦
      li x - (x / log x) * ∑ k ∈ Finset.range n, (k ! : ℝ) / log x ^ k)
      =O[atTop] fun x : ℝ ↦ x / log x ^ (n + 1) := by
  refine ((isBigO_logIntegral_sub_mul_sum n).add
      (isLittleO_const_div_log_pow (li 2) (n + 1)).isBigO).congr'
    ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [li_eq_logIntegral_add_li_two hx]
  ring

/-- `li x ~ Li x` as `x → ∞`. -/
theorem li_isEquivalent_logIntegral : li ~[atTop] logIntegral := by
  rw [Asymptotics.IsEquivalent]
  have ho : (fun _ : ℝ ↦ li 2) =o[atTop] logIntegral :=
    (isLittleO_const_div_log (li 2)).trans_isEquivalent logIntegral_isEquivalent_div_log.symm
  refine ho.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact (sub_eq_of_eq_add' (li_eq_logIntegral_add_li_two hx)).symm

/-- `li x ~ x / log x` as `x → ∞`. -/
theorem li_isEquivalent_div_log : li ~[atTop] fun x : ℝ ↦ x / log x :=
  li_isEquivalent_logIntegral.trans logIntegral_isEquivalent_div_log

/-! ### Numerical enclosures of `li 2 - γ` and `li 2` -/

/-- Sharp lower bound `0.4679475 ≤ li 2 - γ`. -/
theorem le_li_two_sub_eulerMascheroniConstant :
    (0.4679475 : ℝ) ≤ li 2 - eulerMascheroniConstant := by
  rw [li_def]
  linarith [le_log_log_two, le_tsum_log_two_pow_div_mul_factorial]

/-- Sharp upper bound `li 2 - γ ≤ 0.4679495`. -/
theorem li_two_sub_eulerMascheroniConstant_le :
    li 2 - eulerMascheroniConstant ≤ 0.4679495 := by
  rw [li_def]
  linarith [log_log_two_le, tsum_log_two_pow_div_mul_factorial_le]

/-- Unconditional lower bound `0.96 < li 2`. -/
theorem lt_li_two : (0.96 : ℝ) < li 2 := by
  linarith [one_half_lt_eulerMascheroniConstant, le_li_two_sub_eulerMascheroniConstant]

/-- Unconditional upper bound `li 2 < 1.14`. -/
theorem li_two_lt : li 2 < 1.14 := by
  linarith [eulerMascheroniConstant_lt_two_thirds, li_two_sub_eulerMascheroniConstant_le]

/-! ### Bounds and unique zero of `Li x - x / log x` -/

/-- The derivative of `x ↦ Li x - x / log x` on `(1, ∞)` is `(log x ^ 2)⁻¹`. -/
theorem hasDerivAt_logIntegral_sub_div_log {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun t : ℝ ↦ logIntegral t - t / log t) (log x ^ 2)⁻¹ x := by
  have hd := (hasDerivAt_logIntegral hx).fun_sub (hasDerivAt_div_log_pow 1 (log_pos hx).ne')
  simpa only [pow_one, Nat.cast_one, one_mul, sub_sub_cancel] using hd

/-- `x ↦ Li x - x / log x` is strictly increasing on `(1, ∞)`. -/
theorem strictMonoOn_logIntegral_sub_div_log :
    StrictMonoOn (fun x : ℝ ↦ logIntegral x - x / log x) (Ioi 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 1)
    (fun x hx ↦ (hasDerivAt_logIntegral_sub_div_log hx).continuousAt.continuousWithinAt)
    fun x hx ↦ ?_
  rw [interior_Ioi] at hx
  rw [(hasDerivAt_logIntegral_sub_div_log hx).deriv]
  exact inv_pos.mpr (pow_pos (log_pos hx) 2)

/-- Lower bound `x / log x ^ 2 - 2 / log 2 - 2 / log 2 ^ 2 ≤ Li x - x / log x` for `x ≥ 2`. -/
theorem le_logIntegral_sub_div_log {x : ℝ} (hx : 2 ≤ x) :
    x / log x ^ 2 - 2 / log 2 - 2 / log 2 ^ 2 ≤ logIntegral x - x / log x := by
  rw [logIntegral_eq_div_log_sub_add hx, integral_inv_log_pow_eq_sub_add 2 one_lt_two (by linarith)]
  have hnn := integral_inv_log_pow_nonneg 3 one_lt_two hx
  norm_num
  linarith

/-- Strict lower bound `x / log x ^ 2 - 2 / log 2 - 2 / log 2 ^ 2 < Li x - x / log x` for
`x > 2`. -/
theorem lt_logIntegral_sub_div_log {x : ℝ} (hx : 2 < x) :
    x / log x ^ 2 - 2 / log 2 - 2 / log 2 ^ 2 < logIntegral x - x / log x := by
  rw [logIntegral_eq_div_log_sub_add hx.le,
    integral_inv_log_pow_eq_sub_add 2 one_lt_two (by linarith)]
  have hpos : 0 < ∫ t in (2 : ℝ)..x, (log t ^ 3)⁻¹ :=
    lt_of_lt_of_le (div_pos (by linarith) (pow_pos (log_pos (by linarith)) 3))
      (le_integral_inv_log_pow 3 one_lt_two hx.le)
  norm_num
  linarith

/-- Strict upper bound for `Li x - x / log x` on `[2, ∞)`. -/
theorem logIntegral_sub_div_log_lt {x : ℝ} (hx : 2 ≤ x) :
    logIntegral x - x / log x <
      x / log x ^ 2 + 2 * √x / log 2 ^ 3 + 16 * x / log x ^ 3 - 2 / log 2 := by
  rw [logIntegral_eq_div_log_sub_add hx]
  have hb := integral_inv_log_pow_lt_div_add 2 hx
  norm_num at hb ⊢
  have hdist : 2 * (√x / log 2 ^ 3 + 8 * x / log x ^ 3) =
      2 * √x / log 2 ^ 3 + 16 * x / log x ^ 3 := by ring
  linarith

/-- Series representation of `Li x` eliminating the Euler–Mascheroni constant `γ`:
`Li x = log (log x / log 2) + ∑_{n ≥ 1} ((log x)^n - (log 2)^n) / (n * n!)` for `x > 1`. -/
theorem logIntegral_eq_log_div_add_tsum_sub {x : ℝ} (hx : 1 < x) :
    logIntegral x = log (log x / log 2) +
      (∑' n : ℕ, log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) -
      ∑' n : ℕ, log 2 ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
  rw [logIntegral_eq_li_sub_li_two hx, li_def, li_def,
    log_div (log_pos hx).ne' (log_pos one_lt_two).ne']
  ring

private theorem logIntegral_sub_div_log_neg_at :
    logIntegral 6.5797 - 6.5797 / log 6.5797 < 0 := by
  -- Step 1: Upper bound `log 6.5797 ≤ 1.8839895` via `log 6.5797 = 3 log 2 + log (1 - u)`.
  have hlogx : log 6.5797 ≤ 1.8839895 := by
    have hsplit : log 6.5797 = 3 * log 2 + log (1 - 14203 / 80000) := by
      have hprod : (6.5797 : ℝ) = 2 ^ 3 * (1 - 14203 / 80000) := by norm_num
      rw [hprod, log_mul (by norm_num) (by norm_num), log_pow]
      norm_num
    have ht := abs_log_sub_add_sum_range_le (x := (14203 / 80000 : ℝ)) (by norm_num) 8
    rw [abs_le] at ht
    have hupper := ht.2
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at hupper
    norm_num at hupper
    linarith [log_two_lt_d9]
  have hlogx_pos : 0 < log 6.5797 := log_pos (by norm_num)
  -- Step 2: Upper bound `log (log 6.5797 / log 2) ≤ log 6.5797 / (e * log 2)`.
  have hloglog : log (log 6.5797 / log 2) ≤ 1.8839895 / (2.7182818283 * 0.6931471803) := by
    have hr : log 6.5797 / (exp 1 * log 2) ≤ 1.8839895 / (2.7182818283 * 0.6931471803) :=
      div_le_div₀ (by norm_num) hlogx (by norm_num)
        (mul_le_mul exp_one_gt_d9.le log_two_gt_d9.le (by norm_num) (exp_pos 1).le)
    have h1 : log (log 6.5797 / log 2) = 1 + log (log 6.5797 / (exp 1 * log 2)) := by
      rw [log_div hlogx_pos.ne' (log_pos one_lt_two).ne',
        log_div hlogx_pos.ne' (mul_pos (exp_pos 1) (log_pos one_lt_two)).ne',
        log_mul (exp_pos 1).ne' (log_pos one_lt_two).ne', log_exp]
      ring
    have h2 := log_le_sub_one_of_pos
      (div_pos hlogx_pos (mul_pos (exp_pos 1) (log_pos one_lt_two)))
    linarith
  -- Step 3: Upper bound the series at `log 6.5797 ≤ 1.8839895` with 8 terms + geometric tail.
  have hser : (∑' n : ℕ, log 6.5797 ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) ≤
      3.326983 := by
    refine (tsum_pow_div_mul_factorial_mono hlogx).trans ?_
    refine (tsum_pow_div_mul_factorial_le_sum_range_add (y := (1.8839895 : ℝ))
      (by norm_num) (N := 8) (by norm_num)).trans ?_
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]
    norm_num
  -- Step 4: Lower bound `6.5797 / log 6.5797 ≥ 6.5797 / 1.8839895` and combine.
  have hdiv : (6.5797 : ℝ) / 1.8839895 ≤ 6.5797 / log 6.5797 :=
    div_le_div_of_nonneg_left (by norm_num) hlogx_pos hlogx
  rw [logIntegral_eq_log_div_add_tsum_sub (by norm_num)]
  linarith [le_tsum_log_two_pow_div_mul_factorial]

private theorem logIntegral_sub_div_log_pos_at :
    0 < logIntegral 6.5798 - 6.5798 / log 6.5798 := by
  -- Step 1: Lower bound `1.884004 ≤ log 6.5798` via `log 6.5798 = 3 log 2 + log (1 - u)`.
  have hlogx : (1.884004 : ℝ) ≤ log 6.5798 := by
    have hsplit : log 6.5798 = 3 * log 2 + log (1 - 7101 / 40000) := by
      have hprod : (6.5798 : ℝ) = 2 ^ 3 * (1 - 7101 / 40000) := by norm_num
      rw [hprod, log_mul (by norm_num) (by norm_num), log_pow]
      norm_num
    have ht := abs_log_sub_add_sum_range_le (x := (7101 / 40000 : ℝ)) (by norm_num) 8
    rw [abs_le] at ht
    have hlower := ht.1
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at hlower
    norm_num at hlower
    linarith [log_two_gt_d9]
  have hlogx_pos : 0 < log 6.5798 := by linarith
  -- Step 2: Lower bound `log (log 6.5798 / log 2) ≥ 2 - (e * log 2) / log 6.5798`.
  have hloglog : 2 - (2.7182818286 * 0.6931471808) / 1.884004 ≤
      log (log 6.5798 / log 2) := by
    have hinv : (exp 1 * log 2) / log 6.5798 ≤ (2.7182818286 * 0.6931471808) / 1.884004 :=
      div_le_div₀ (by norm_num)
        (mul_le_mul exp_one_lt_d9.le log_two_lt_d9.le (log_pos one_lt_two).le (by norm_num))
        (by norm_num) hlogx
    have h1 : log (log 6.5798 / log 2) = 1 + log (log 6.5798 / (exp 1 * log 2)) := by
      rw [log_div hlogx_pos.ne' (log_pos one_lt_two).ne',
        log_div hlogx_pos.ne' (mul_pos (exp_pos 1) (log_pos one_lt_two)).ne',
        log_mul (exp_pos 1).ne' (log_pos one_lt_two).ne', log_exp]
      ring
    have h2 := one_sub_inv_le_log_of_pos
      (div_pos hlogx_pos (mul_pos (exp_pos 1) (log_pos one_lt_two)))
    rw [inv_div] at h2
    linarith
  -- Step 3: Lower bound the series at `log 6.5798 ≥ 1.884004` with 10 terms.
  have hser : (3.327019 : ℝ) ≤
      ∑' n : ℕ, log 6.5798 ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
    refine le_trans ?_ (tsum_pow_div_mul_factorial_mono hlogx)
    refine le_trans ?_ (sum_range_le_tsum_pow_div_mul_factorial (y := (1.884004 : ℝ))
      (by norm_num) 10)
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]
    norm_num
  -- Step 4: Upper bound `6.5798 / log 6.5798 ≤ 6.5798 / 1.884004` and combine.
  have hdiv : 6.5798 / log 6.5798 ≤ 6.5798 / 1.884004 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlogx
  rw [logIntegral_eq_log_div_add_tsum_sub (by norm_num)]
  linarith [tsum_log_two_pow_div_mul_factorial_le]

/-- `Li x - x / log x < 0` for every `1 < x ≤ 6.5797`. -/
theorem logIntegral_sub_div_log_neg {x : ℝ} (hx1 : 1 < x) (hx : x ≤ 6.5797) :
    logIntegral x - x / log x < 0 := by
  rcases eq_or_lt_of_le hx with rfl | hlt
  · exact logIntegral_sub_div_log_neg_at
  · exact (strictMonoOn_logIntegral_sub_div_log hx1 (by norm_num) hlt).trans
      logIntegral_sub_div_log_neg_at

/-- `0 < Li x - x / log x` for every `x ≥ 6.5798`. -/
theorem logIntegral_sub_div_log_pos {x : ℝ} (hx : 6.5798 ≤ x) :
    0 < logIntegral x - x / log x := by
  rcases eq_or_lt_of_le hx with rfl | hlt
  · exact logIntegral_sub_div_log_pos_at
  · exact logIntegral_sub_div_log_pos_at.trans
      (strictMonoOn_logIntegral_sub_div_log (by norm_num) (mem_Ioi.mpr (by linarith)) hlt)

/-- `Li x - x / log x` has a unique zero in `(6.5797, 6.5798)`. -/
theorem existsUnique_logIntegral_sub_div_log_eq_zero_Ioo :
    ∃! x ∈ Ioo (6.5797 : ℝ) 6.5798, logIntegral x - x / log x = 0 := by
  have hcont : ContinuousOn (fun t : ℝ ↦ logIntegral t - t / log t) (Icc 6.5797 6.5798) :=
    fun t ht ↦
      (hasDerivAt_logIntegral_sub_div_log (by linarith [ht.1])).continuousAt.continuousWithinAt
  have h0 : (0 : ℝ) ∈ Icc (logIntegral 6.5797 - 6.5797 / log 6.5797)
      (logIntegral 6.5798 - 6.5798 / log 6.5798) :=
    ⟨logIntegral_sub_div_log_neg_at.le, logIntegral_sub_div_log_pos_at.le⟩
  obtain ⟨x₀, hx₀, hfx₀⟩ := intermediate_value_Icc (by norm_num) hcont h0
  have hx₀_lt : 6.5797 < x₀ := lt_of_le_of_ne hx₀.1 fun h ↦ by
    subst h; linarith [logIntegral_sub_div_log_neg_at]
  have hx₀_gt : x₀ < 6.5798 := lt_of_le_of_ne hx₀.2 fun h ↦ by
    subst h; linarith [logIntegral_sub_div_log_pos_at]
  refine ⟨x₀, ⟨⟨hx₀_lt, hx₀_gt⟩, hfx₀⟩, fun y ⟨hy, hfy⟩ ↦ ?_⟩
  exact strictMonoOn_logIntegral_sub_div_log.injOn (mem_Ioi.mpr (by linarith [hy.1]))
    (mem_Ioi.mpr (by linarith [hx₀_lt])) (hfy.trans hfx₀.symm)

/-- `Li x - x / log x` has a unique zero in `(1, ∞)`. -/
theorem existsUnique_logIntegral_sub_div_log_eq_zero :
    ∃! x ∈ Ioi (1 : ℝ), logIntegral x - x / log x = 0 := by
  obtain ⟨x₀, ⟨⟨hx₀_lo, _⟩, hfx₀⟩, _⟩ := existsUnique_logIntegral_sub_div_log_eq_zero_Ioo
  refine ⟨x₀, ⟨mem_Ioi.mpr (by linarith), hfx₀⟩, fun y ⟨hy, hfy⟩ ↦ ?_⟩
  exact strictMonoOn_logIntegral_sub_div_log.injOn hy (mem_Ioi.mpr (by linarith))
    (hfy.trans hfx₀.symm)

/-- **Fiori–Kadiri–Swidinsky (2023), Lemma 20**: for every `x ≥ 6.58`,
`(x - 6.58) / log x ^ 2 ≤ Li x - x / log x`. -/
theorem sub_div_log_sq_le_logIntegral_sub_div_log {x : ℝ} (hx : 6.58 ≤ x) :
    (x - 6.58) / log x ^ 2 ≤ logIntegral x - x / log x := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (6.58 : ℝ)) (b := x)
    (f := fun t : ℝ ↦ logIntegral t - t / log t)
    (f' := fun t : ℝ ↦ (log t ^ 2)⁻¹)
    (fun t ht ↦ by
      rw [uIcc_of_le hx] at ht
      exact hasDerivAt_logIntegral_sub_div_log (by linarith [ht.1]))
    (intervalIntegrable_inv_log_pow 2 (by norm_num) (by linarith))
  have hpos : 0 < logIntegral 6.58 - 6.58 / log 6.58 :=
    logIntegral_sub_div_log_pos (by norm_num)
  have hlow := le_integral_inv_log_pow 2 (by norm_num : (1 : ℝ) < 6.58) hx
  linarith

end Real
