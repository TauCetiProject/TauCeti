/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.LogIntegral.Unoffset
import Mathlib.Analysis.Complex.ExponentialBounds
import TauCeti.Analysis.SpecialFunctions.Exp.ExpIntegralSeries
import TauCeti.Analysis.SpecialFunctions.Integrals.InvLog
import TauCeti.Analysis.SpecialFunctions.Log.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Log.Bounds
import TauCeti.Analysis.SpecialFunctions.Log.NegLogOneSub

/-!
# Explicit bounds and asymptotic expansion for the logarithmic integral

These bounds translate between the offset logarithmic integral `TauCeti.Real.logIntegral` (`Li`),
the unoffset logarithmic integral `TauCeti.Real.li`, and explicit `x / log x ^ k` approximations in
prime-counting estimates. The enclosure `0.4679475 ≤ li 2 - γ ≤ 0.4679495` turns any enclosure of
the Euler–Mascheroni constant `γ` into one of `li 2`: combined with `1 / 2 < γ < 2 / 3` it gives
the unconditional enclosure `0.96 < li 2 < 1.14`, and under `|γ - 0.5772156649| < 10⁻⁹` it gives
`1.0451 ≤ li 2 ≤ 1.0452`.

* **Asymptotic expansion**: repeated integration by parts gives
  `li x - (x / log x) * ∑ k ∈ range n, k! / log x ^ k = O(x / log x ^ (n + 1))` as `x → ∞`,
  together with `li ~ Li ~ x / log x`.
* **Numerical enclosures of `li 2 - γ` and `li 2`**: combining the `y = log 2` series enclosure
  `∑_{n ≥ 1} (log 2)^n / (n * n!) ∈ [0.8344605, 0.8344615]` (via the partial-sum and
  geometric-tail bounds in `TauCeti.Analysis.SpecialFunctions.Exp.ExpIntegralSeries`) with
  `log (log 2) ∈ [-0.366513, -0.366512]` yields `0.4679475 ≤ li 2 - γ ≤ 0.4679495`, the
  unconditional enclosure `0.96 < li 2 < 1.14`, and conditional enclosures `1.0451 ≤ li 2 ≤ 1.0452`
  assuming `|γ - 0.5772156649| < 10⁻⁹`.
* **Zero localization and Fiori–Kadiri–Swidinsky lower bound for `Li x - x / log x`**: localization
  of the unique zero in `(6.5797, 6.5798)` and `(1, ∞)`, sign bounds away from `(6.5797, 6.5798)`,
  and Fiori–Kadiri–Swidinsky's lower bound `(x - 6.58) / log x ^ 2 ≤ Li x - x / log x` for
  `x ≥ 6.58`.

## Main declarations

* `TauCeti.Real.isBigO_li_sub_mul_sum`, `TauCeti.Real.li_isEquivalent_logIntegral`,
  `TauCeti.Real.li_isEquivalent_div_log` — asymptotic expansion and prime-number-theorem
  equivalences for `li`.
* `TauCeti.Real.le_tsum_log_two_pow_div_mul_factorial`,
  `TauCeti.Real.tsum_log_two_pow_div_mul_factorial_le`,
  `TauCeti.Real.le_li_two_sub_eulerMascheroniConstant`,
  `TauCeti.Real.li_two_sub_eulerMascheroniConstant_le`, `TauCeti.Real.lt_li_two`,
  `TauCeti.Real.li_two_lt`, `TauCeti.Real.le_li_two_of_abs_eulerMascheroniConstant_sub_lt`,
  `TauCeti.Real.li_two_le_of_abs_eulerMascheroniConstant_sub_lt` — enclosures of the `y = log 2`
  entire-part series, `li 2 - γ`, and `li 2`.
* `TauCeti.Real.logIntegral_eq_log_div_add_tsum_sub`,
  `TauCeti.Real.existsUnique_logIntegral_sub_div_log_eq_zero_Ioi`,
  `TauCeti.Real.existsUnique_logIntegral_sub_div_log_eq_zero_Ioo`,
  `TauCeti.Real.logIntegral_sub_div_log_neg`, `TauCeti.Real.logIntegral_sub_div_log_pos`,
  `TauCeti.Real.sub_div_log_sq_le_logIntegral_sub_div_log` — series representation eliminating `γ`,
  unique zero, sign bounds, and Fiori–Kadiri–Swidinsky Lemma 20 for `Li x - x / log x`.

## References

* F. W. J. Olver et al., *NIST Digital Library of Mathematical Functions*, §3.12 (eq. 3.12.4, for
  the digits of `γ` implying `|γ - 0.5772156649| < 10⁻⁹`), §6.2, and §6.12.
* O. Ramaré and R. Rumely, *Primes in arithmetic progressions*, *Math. Comp.* 65 (1996)
  (for the decimal approximation of `γ`).
* A. Fiori, H. Kadiri, and J. Swidinsky, *Sharper bounds for the error term in the prime number
  theorem*, *Res. Number Theory* 9 (2023), Article 63, Lemma 20.
-/

public section

open Asymptotics Filter MeasureTheory Set Real
open scoped Topology Nat

namespace TauCeti.Real

/-! ### Asymptotic expansion of `li` -/

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

/-- Explicit decimal lower bound `0.8344605 ≤ ∑_{n ≥ 1} (log 2)^n / (n * n!)`. -/
theorem le_tsum_log_two_pow_div_mul_factorial :
    (0.8344605 : ℝ) ≤
      ∑' n : ℕ, log 2 ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
  have hlog : (0.693147 : ℝ) ≤ log 2 := le_trans (by norm_num) log_two_gt_d9.le
  refine le_trans ?_ (tsum_pow_div_mul_factorial_mono hlog)
  refine le_trans ?_ (sum_range_le_tsum_pow_div_mul_factorial (y := (0.693147 : ℝ)) (by norm_num) 7)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]
  norm_num

/-- Explicit decimal upper bound `∑_{n ≥ 1} (log 2)^n / (n * n!) ≤ 0.8344615`. -/
theorem tsum_log_two_pow_div_mul_factorial_le :
    (∑' n : ℕ, log 2 ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) ≤ 0.8344615 := by
  have hlog : log 2 ≤ 0.6931472 := le_trans log_two_lt_d9.le (by norm_num)
  refine (tsum_pow_div_mul_factorial_mono hlog).trans ?_
  refine (tsum_pow_div_mul_factorial_le_sum_range_add (y := (0.6931472 : ℝ))
    (by norm_num) (N := 7) (by norm_num)).trans ?_
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]
  norm_num

/-- Explicit decimal lower bound `0.4679475 ≤ li 2 - γ`. -/
theorem le_li_two_sub_eulerMascheroniConstant :
    (0.4679475 : ℝ) ≤ li 2 - eulerMascheroniConstant := by
  rw [li_def]
  linarith [le_log_log_two, le_tsum_log_two_pow_div_mul_factorial]

/-- Explicit decimal upper bound `li 2 - γ ≤ 0.4679495`. -/
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

/-- Conditional lower bound `1.0451 ≤ li 2` under `|γ - 0.5772156649| < 10⁻⁹`. -/
theorem le_li_two_of_abs_eulerMascheroniConstant_sub_lt
    (hγ : |eulerMascheroniConstant - 0.5772156649| < 10 ^ (-(9 : ℤ))) :
    (1.0451 : ℝ) ≤ li 2 := by
  rw [abs_lt] at hγ
  norm_num at hγ
  linarith [hγ.1, le_li_two_sub_eulerMascheroniConstant]

/-- Conditional upper bound `li 2 ≤ 1.0452` under `|γ - 0.5772156649| < 10⁻⁹`. -/
theorem li_two_le_of_abs_eulerMascheroniConstant_sub_lt
    (hγ : |eulerMascheroniConstant - 0.5772156649| < 10 ^ (-(9 : ℤ))) :
    li 2 ≤ 1.0452 := by
  rw [abs_lt] at hγ
  norm_num at hγ
  linarith [hγ.2, li_two_sub_eulerMascheroniConstant_le]

/-! ### Zero localization and Lemma 20 for `Li x - x / log x` -/

/-- Series representation of `Li x` eliminating the Euler–Mascheroni constant `γ`:
`Li x = log (log x / log 2) + ∑_{n ≥ 1} ((log x)^n - (log 2)^n) / (n * n!)` for `x > 1`. -/
theorem logIntegral_eq_log_div_add_tsum_sub {x : ℝ} (hx : 1 < x) :
    logIntegral x = log (log x / log 2) +
      (∑' n : ℕ, log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) -
      ∑' n : ℕ, log 2 ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
  rw [logIntegral_eq_li_sub_li_two hx, li_def, li_def,
    log_div (log_pos hx).ne' (log_pos one_lt_two).ne']
  ring

private theorem log_eight : log (8 : ℝ) = 3 * log 2 := by
  have h8 : (8 : ℝ) = 2 ^ 3 := by norm_num
  rw [h8, log_pow]
  norm_num

private theorem log_div_log_two_eq_one_add {L : ℝ} (hL : 0 < L) :
    log (L / log 2) = 1 + log (L / (exp 1 * log 2)) := by
  rw [log_div hL.ne' (log_pos one_lt_two).ne',
    log_div hL.ne' (mul_pos (exp_pos 1) (log_pos one_lt_two)).ne',
    log_mul (exp_pos 1).ne' (log_pos one_lt_two).ne', log_exp]
  ring

private theorem logIntegral_sub_div_log_neg_at :
    logIntegral 6.5797 - 6.5797 / log 6.5797 < 0 := by
  -- Step 1: Upper bound `log 6.5797 ≤ 1.8839895` via `6.5797 = 8 * (1 - 14203 / 80000)`.
  have hlogx : log 6.5797 ≤ 1.8839895 := by
    have hupper := (abs_le.mp (abs_log_mul_one_sub_sub_le
      (c := (8 : ℝ)) (u := (14203 / 80000 : ℝ)) (by norm_num) (by norm_num) 8)).2
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at hupper
    norm_num [log_eight] at hupper
    linarith [log_two_lt_d9]
  have hlogx_pos : 0 < log 6.5797 := log_pos (by norm_num)
  -- Step 2: Upper bound `log (log 6.5797 / log 2) ≤ log 6.5797 / (e * log 2)`.
  have hloglog : log (log 6.5797 / log 2) ≤ 1.8839895 / (2.7182818283 * 0.6931471803) := by
    have hr : log 6.5797 / (exp 1 * log 2) ≤ 1.8839895 / (2.7182818283 * 0.6931471803) :=
      div_le_div₀ (by norm_num) hlogx (by norm_num)
        (mul_le_mul exp_one_gt_d9.le log_two_gt_d9.le (by norm_num) (exp_pos 1).le)
    have h1 := log_div_log_two_eq_one_add hlogx_pos
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
  -- Step 1: Lower bound `1.884004 ≤ log 6.5798` via `6.5798 = 8 * (1 - 7101 / 40000)`.
  have hlogx : (1.884004 : ℝ) ≤ log 6.5798 := by
    have hlower := (abs_le.mp (abs_log_mul_one_sub_sub_le
      (c := (8 : ℝ)) (u := (7101 / 40000 : ℝ)) (by norm_num) (by norm_num) 8)).1
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at hlower
    norm_num [log_eight] at hlower
    linarith [log_two_gt_d9]
  have hlogx_pos : 0 < log 6.5798 := by linarith
  -- Step 2: Lower bound `log (log 6.5798 / log 2) ≥ 2 - (e * log 2) / log 6.5798`.
  have hloglog : 2 - (2.7182818286 * 0.6931471808) / 1.884004 ≤
      log (log 6.5798 / log 2) := by
    have hinv : (exp 1 * log 2) / log 6.5798 ≤ (2.7182818286 * 0.6931471808) / 1.884004 :=
      div_le_div₀ (by norm_num)
        (mul_le_mul exp_one_lt_d9.le log_two_lt_d9.le (log_pos one_lt_two).le (by norm_num))
        (by norm_num) hlogx
    have h1 := log_div_log_two_eq_one_add hlogx_pos
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
theorem existsUnique_logIntegral_sub_div_log_eq_zero_Ioi :
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

end TauCeti.Real
