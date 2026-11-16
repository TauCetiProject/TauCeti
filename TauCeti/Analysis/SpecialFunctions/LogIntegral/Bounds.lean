/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.LogIntegral.Principal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Explicit bounds and asymptotic expansion for the logarithmic integral

This file proves explicit integral bounds, the asymptotic expansion of `Li` and `li`, numerical
enclosures of `li`, and comparison inequalities between `Li x` and `x / log x`.

## Main declarations

* `TauCeti.Real.integral_inv_log_rpow_eq_sub_add`,
  `TauCeti.Real.integral_inv_log_rpow_le_sqrt_add`,
  `TauCeti.Real.integral_inv_log_rpow_lt` — integration by parts and explicit two-sided bounds for
  `∫₂ˣ dt / log ^ k t` for real exponents `k` (with natural-exponent corollaries
  `TauCeti.Real.integral_inv_log_pow_le_sqrt_add` and `TauCeti.Real.integral_inv_log_pow_lt`,
  covering in particular `k = 7`).
* `TauCeti.Real.logIntegral_eq_sum_add_integral`,
  `TauCeti.Real.logIntegral_sub_sum_isBigO`,
  `TauCeti.Real.principalLogIntegral_sub_sum_isBigO`,
  `TauCeti.Real.principalLogIntegral_isEquivalent_div_log` — the full asymptotic expansion
  `li x = (x / log x) ∑_{k < n} k! / (log x) ^ k + O(x / (log x) ^ (n + 1))`.
* `TauCeti.Real.principalLogIntegral_pos_of_three_halves_le` — `li x > 0` for `x ≥ 3 / 2`.
* `TauCeti.Real.tsum_log_two_pow_div_ge`, `TauCeti.Real.tsum_log_two_pow_div_le`,
  `TauCeti.Real.log_log_two_ge`, `TauCeti.Real.log_log_two_le`,
  `TauCeti.Real.principalLogIntegral_two_sub_eulerGamma_ge`,
  `TauCeti.Real.principalLogIntegral_two_sub_eulerGamma_le`,
  `TauCeti.Real.principalLogIntegral_two_gt`, `TauCeti.Real.principalLogIntegral_two_lt`,
  `TauCeti.Real.principalLogIntegral_two_ge_of_eulerGamma`,
  `TauCeti.Real.principalLogIntegral_two_le_of_eulerGamma` — unconditional enclosures of
  `li 2 - γ` and `li 2` (`0.96 < li 2 < 1.14`), conditional enclosure `1.0451 ≤ li 2 ≤ 1.0452`,
  and `li ≠ Li`.
* `TauCeti.Real.strictMonoOn_logIntegral_sub_div_log`,
  `TauCeti.Real.le_logIntegral_sub_div_log`, `TauCeti.Real.logIntegral_sub_div_log_lt`,
  `TauCeti.Real.existsUnique_logIntegral_eq_div_log`,
  `TauCeti.Real.existsUnique_logIntegral_eq_div_log_Ioo`,
  `TauCeti.Real.sub_div_log_sq_lt_logIntegral_sub_div_log`, `TauCeti.Real.div_log_lt_logIntegral` —
  monotonicity, two-sided explicit bounds, unique root in `(6.5797, 6.5798)`, and the strict
  lower bound `(x - 6.58) / (log x) ^ 2 < Li x - x / log x` for every `x > 1`.

## References

* A. Fiori, H. Kadiri, and J. Swidinsky, *Sharper bounds for the Chebyshev function `ψ(x)`*,
  J. Math. Anal. Appl. 527 (2023), 127426, Lemma 20.
* L. Schoenfeld, *Sharper bounds for the Chebyshev functions `θ(x)` and `ψ(x)`. II*,
  Math. Comp. 30 (1976), 337–360.
-/

public section

namespace TauCeti.Real

open Asymptotics Filter MeasureTheory Set
open scoped Topology Nat

/-! ### Explicit integrals of reciprocal real powers of `log` -/

/-- Reciprocal real powers of the logarithm are continuous on `(1, ∞)`. -/
theorem continuousOn_inv_log_rpow (k : ℝ) :
    ContinuousOn (fun t : ℝ ↦ (Real.log t ^ k)⁻¹) (Ioi 1) := by
  have hlog : ContinuousOn Real.log (Ioi 1) :=
    Real.continuousOn_log.mono fun t (ht : 1 < t) ↦ (zero_lt_one.trans ht).ne'
  refine (hlog.rpow_const fun t ht ↦ Or.inl (Real.log_pos ht).ne').inv₀ fun t ht ↦ ?_
  exact (Real.rpow_pos_of_pos (Real.log_pos ht) k).ne'

/-- Reciprocal real powers of the logarithm are interval integrable on any interval in `(1, ∞)`. -/
theorem intervalIntegrable_inv_log_rpow (k : ℝ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t : ℝ ↦ (Real.log t ^ k)⁻¹) volume a b := by
  refine ((continuousOn_inv_log_rpow k).mono fun t ht ↦ ?_).intervalIntegrable
  rcases mem_uIcc.mp ht with h | h
  · exact ha.trans_le h.1
  · exact hb.trans_le h.1

/-- The integral `∫ t in a..b, (log t ^ k)⁻¹` is nonnegative for `1 < a ≤ b`. -/
theorem integral_inv_log_rpow_nonneg (k : ℝ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    0 ≤ ∫ t in a..b, (Real.log t ^ k)⁻¹ := by
  refine intervalIntegral.integral_nonneg hab fun t ht ↦ ?_
  have hlog : 0 < Real.log t := Real.log_pos (ha.trans_le ht.1)
  positivity

/-- Monotonicity upper bound `∫ t in a..b, (log t ^ k)⁻¹ ≤ (b - a) / log a ^ k` for `k ≥ 0`. -/
theorem integral_inv_log_rpow_le {k : ℝ} (hk : 0 ≤ k) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in a..b, (Real.log t ^ k)⁻¹) ≤ (b - a) / Real.log a ^ k := by
  have hla : 0 < Real.log a := Real.log_pos ha
  have hb : 1 < b := ha.trans_le hab
  have hmono := intervalIntegral.integral_mono_on hab (intervalIntegrable_inv_log_rpow k ha hb)
    (g := fun _ ↦ (Real.log a ^ k)⁻¹) intervalIntegrable_const fun t ht ↦
      inv_anti₀ (Real.rpow_pos_of_pos hla k)
        (Real.rpow_le_rpow hla.le (Real.log_le_log (zero_lt_one.trans ha) ht.1) hk)
  simpa [smul_eq_mul, div_eq_mul_inv] using hmono

/-- Monotonicity lower bound `(b - a) / log b ^ k ≤ ∫ t in a..b, (log t ^ k)⁻¹` for `k ≥ 0`. -/
theorem le_integral_inv_log_rpow {k : ℝ} (hk : 0 ≤ k) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (b - a) / Real.log b ^ k ≤ ∫ t in a..b, (Real.log t ^ k)⁻¹ := by
  have hb : 1 < b := ha.trans_le hab
  have hmono := intervalIntegral.integral_mono_on hab
    (f := fun _ ↦ (Real.log b ^ k)⁻¹) intervalIntegrable_const
    (intervalIntegrable_inv_log_rpow k ha hb) fun t ht ↦ by
      have hlt : 0 < Real.log t := Real.log_pos (ha.trans_le ht.1)
      exact inv_anti₀ (Real.rpow_pos_of_pos hlt k)
        (Real.rpow_le_rpow hlt.le (Real.log_le_log (zero_lt_one.trans (ha.trans_le ht.1)) ht.2) hk)
  simpa [smul_eq_mul, div_eq_mul_inv] using hmono

/-- Integration by parts for reciprocal real powers of the logarithm on `(1, ∞)`. -/
theorem integral_inv_log_rpow_eq_sub_add (k : ℝ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    (∫ t in a..b, (Real.log t ^ k)⁻¹) = b / Real.log b ^ k - a / Real.log a ^ k +
      k * ∫ t in a..b, (Real.log t ^ (k + 1))⁻¹ := by
  have hi := intervalIntegrable_inv_log_rpow k ha hb
  have hi1 := intervalIntegrable_inv_log_rpow (k + 1) ha hb
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hasDerivAt_div_log_rpow k (Real.log_pos (by
      rcases mem_uIcc.mp ht with h | h
      · exact ha.trans_le h.1
      · exact hb.trans_le h.1)).ne') (hi.sub (hi1.const_mul k))
  rw [intervalIntegral.integral_sub hi (hi1.const_mul k),
    intervalIntegral.integral_const_mul] at hFTC
  exact sub_eq_iff_eq_add.mp hFTC

/-- Splitting at `√x` gives `∫₂ˣ dt / log ^ k t ≤ √x / log ^ k 2 + 2 ^ k * x / log ^ k x` for
every real `k ≥ 0` and `x > 1`. -/
theorem integral_inv_log_rpow_le_sqrt_add {k : ℝ} (hk : 0 ≤ k) {x : ℝ} (hx : 1 < x) :
    (∫ t in (2 : ℝ)..x, (Real.log t ^ k)⁻¹) ≤
      √x / Real.log 2 ^ k + 2 ^ k * x / Real.log x ^ k := by
  have hx0 : (0 : ℝ) < x := zero_lt_one.trans hx
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogx : 0 < Real.log x := Real.log_pos hx
  rcases lt_or_ge x 2 with hlt | h2
  · have hneg : (∫ t in (2 : ℝ)..x, (Real.log t ^ k)⁻¹) ≤ 0 := by
      rw [intervalIntegral.integral_symm]
      exact neg_nonpos.mpr (integral_inv_log_rpow_nonneg k hx hlt.le)
    have hrhs : 0 ≤ √x / Real.log 2 ^ k + 2 ^ k * x / Real.log x ^ k := by positivity
    exact hneg.trans hrhs
  have hsqrt4 : √(4 : ℝ) = 2 := by rw [← Real.sqrt_sq zero_le_two]; norm_num
  rcases le_or_gt 4 x with h4 | h4
  · have hsq : 2 ≤ √x := hsqrt4 ▸ Real.sqrt_le_sqrt h4
    have hle : √x ≤ x := Real.sqrt_le_self_iff.mpr (Or.inr (by linarith))
    have hsplit : (∫ t in (2 : ℝ)..x, (Real.log t ^ k)⁻¹) =
        (∫ t in (2 : ℝ)..√x, (Real.log t ^ k)⁻¹) + ∫ t in √x..x, (Real.log t ^ k)⁻¹ :=
      (intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_inv_log_rpow k one_lt_two (by linarith))
        (intervalIntegrable_inv_log_rpow k (by linarith) hx)).symm
    have hb₁ : (∫ t in (2 : ℝ)..√x, (Real.log t ^ k)⁻¹) ≤ √x / Real.log 2 ^ k :=
      (integral_inv_log_rpow_le hk one_lt_two hsq).trans
        (div_le_div_of_nonneg_right (by linarith) (Real.rpow_nonneg hlog2.le k))
    have hb₂ : (∫ t in √x..x, (Real.log t ^ k)⁻¹) ≤ 2 ^ k * x / Real.log x ^ k := by
      refine (integral_inv_log_rpow_le hk (by linarith) hle).trans ?_
      rw [Real.log_sqrt hx0.le, Real.div_rpow hlogx.le zero_le_two,
        div_div_eq_mul_div, mul_comm (x - √x)]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith [Real.sqrt_nonneg x]) (by positivity))
        (Real.rpow_nonneg hlogx.le k)
    linarith
  · have hlog_le : Real.log x / 2 ≤ Real.log 2 := by
      rw [← Real.log_sqrt hx0.le]
      exact Real.log_le_log (Real.sqrt_pos.mpr hx0)
        (hsqrt4 ▸ (Real.sqrt_lt_sqrt hx0.le h4).le)
    have hpow : (Real.log x / 2) ^ k ≤ Real.log 2 ^ k :=
      Real.rpow_le_rpow (by positivity) hlog_le hk
    have hmain : (x - 2) / Real.log 2 ^ k ≤ 2 ^ k * x / Real.log x ^ k := by
      calc (x - 2) / Real.log 2 ^ k ≤ x / (Real.log x / 2) ^ k :=
            div_le_div₀ hx0.le (by linarith) (by positivity) hpow
        _ = 2 ^ k * x / Real.log x ^ k := by
            rw [Real.div_rpow hlogx.le zero_le_two, div_div_eq_mul_div, mul_comm]
    have hnn : 0 ≤ √x / Real.log 2 ^ k := by positivity
    linarith [integral_inv_log_rpow_le hk one_lt_two h2]

/-- Explicit upper bound obtained by one integration by parts followed by splitting at `√x`:
for `k ≥ 0` and `x > 1`, `∫₂ˣ dt / log ^ k t` is strictly bounded above by
`x / log ^ k x + k * (√x / log ^ (k + 1) 2 + 2 ^ (k + 1) * x / log ^ (k + 1) x)`. -/
theorem integral_inv_log_rpow_lt {k : ℝ} (hk : 0 ≤ k) {x : ℝ} (hx : 1 < x) :
    (∫ t in (2 : ℝ)..x, (Real.log t ^ k)⁻¹) <
      x / Real.log x ^ k +
        k * (√x / Real.log 2 ^ (k + 1) + 2 ^ (k + 1) * x / Real.log x ^ (k + 1)) := by
  have hibp := integral_inv_log_rpow_eq_sub_add k one_lt_two hx
  have htail := integral_inv_log_rpow_le_sqrt_add (k := k + 1) (by linarith) hx
  have hpos : 0 < 2 / Real.log 2 ^ k :=
    div_pos two_pos (Real.rpow_pos_of_pos (Real.log_pos one_lt_two) k)
  nlinarith

/-- Natural-exponent form of `TauCeti.Real.integral_inv_log_rpow_le_sqrt_add`. -/
theorem integral_inv_log_pow_le_sqrt_add (n : ℕ) {x : ℝ} (hx : 1 < x) :
    (∫ t in (2 : ℝ)..x, (Real.log t ^ n)⁻¹) ≤
      √x / Real.log 2 ^ n + 2 ^ n * x / Real.log x ^ n := by
  simpa only [Real.rpow_natCast] using
    integral_inv_log_rpow_le_sqrt_add (k := (n : ℝ)) (Nat.cast_nonneg n) hx

/-- Natural-exponent form of `TauCeti.Real.integral_inv_log_rpow_lt` (in particular, `n = 7` gives
`∫₂ˣ dt / log ^ 7 t < x / log ^ 7 x + 7 * (√x / log ^ 8 2 + 2 ^ 8 * x / log ^ 8 x)`). -/
theorem integral_inv_log_pow_lt (n : ℕ) {x : ℝ} (hx : 1 < x) :
    (∫ t in (2 : ℝ)..x, (Real.log t ^ n)⁻¹) <
      x / Real.log x ^ n +
        (n : ℝ) * (√x / Real.log 2 ^ (n + 1) + 2 ^ (n + 1) * x / Real.log x ^ (n + 1)) := by
  have h := integral_inv_log_rpow_lt (k := (n : ℝ)) (Nat.cast_nonneg n) hx
  simpa only [← Nat.cast_add_one, Real.rpow_natCast] using h

/-! ### Asymptotic expansion of `Li` and `li` -/

/-- Exact `n`-step integration-by-parts expansion of the offset logarithmic integral `Li x`. -/
theorem logIntegral_eq_sum_add_integral (n : ℕ) {x : ℝ} (hx : 1 < x) :
    logIntegral x =
      (x / Real.log x) * (∑ k ∈ Finset.range n, (k ! : ℝ) / Real.log x ^ k) -
        (2 / Real.log 2) * (∑ k ∈ Finset.range n, (k ! : ℝ) / Real.log 2 ^ k) +
        (n ! : ℝ) * ∫ t in (2 : ℝ)..x, (Real.log t ^ (n + 1))⁻¹ := by
  induction n with
  | zero => simp [logIntegral_def]
  | succ n ih =>
    rw [ih, integral_inv_log_pow_eq_sub_add (n + 1) one_lt_two hx,
      Finset.sum_range_succ, Finset.sum_range_succ, Nat.factorial_succ]
    push_cast
    have hx_term : (n ! : ℝ) * (x / Real.log x ^ (n + 1)) =
        (x / Real.log x) * ((n ! : ℝ) / Real.log x ^ n) := by
      rw [pow_succ']; ring
    have h2_term : (n ! : ℝ) * (2 / Real.log 2 ^ (n + 1)) =
        (2 / Real.log 2) * ((n ! : ℝ) / Real.log 2 ^ n) := by
      rw [pow_succ']; ring
    linarith

/-- For every `n : ℕ`, `∫₂ˣ dt / log ^ n t = O(x / log ^ n x)` as `x → ∞`. -/
theorem integral_inv_log_pow_isBigO (n : ℕ) :
    (fun x : ℝ ↦ ∫ t in (2 : ℝ)..x, (Real.log t ^ n)⁻¹) =O[atTop]
      fun x : ℝ ↦ x / Real.log x ^ n := by
  have hlog2_pos : 0 < Real.log 2 ^ n := pow_pos (Real.log_pos one_lt_two) n
  have hlo := (_root_.isLittleO_log_rpow_rpow_atTop (n : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)).bound hlog2_pos
  refine IsBigO.of_bound (1 + 2 ^ n) ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ), hlo] with x hx hbound
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hsq : Real.log x ^ n ≤ Real.log 2 ^ n * √x := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_natCast, ← Real.sqrt_eq_rpow,
      abs_of_pos (pow_pos hlogx n), abs_of_pos (Real.sqrt_pos.mpr hx0)] at hbound
    exact hbound
  have hsqrt_le : √x / Real.log 2 ^ n ≤ x / Real.log x ^ n := by
    rw [div_le_div_iff₀ (pow_pos hlog2 n) (pow_pos hlogx n)]
    have hmul : √x * √x = x := Real.mul_self_sqrt hx0.le
    calc √x * Real.log x ^ n ≤ √x * (Real.log 2 ^ n * √x) :=
          mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg x)
      _ = x * Real.log 2 ^ n := by rw [← mul_assoc, mul_comm √x, mul_assoc, hmul, mul_comm]
  have hnn : 0 ≤ ∫ t in (2 : ℝ)..x, (Real.log t ^ n)⁻¹ :=
    integral_inv_log_pow_nonneg n one_lt_two hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn,
    abs_of_pos (div_pos hx0 (pow_pos hlogx n))]
  have hup := integral_inv_log_pow_le_sqrt_add n (one_lt_two.trans_le hx)
  have hrhs : (1 + 2 ^ n) * (x / Real.log x ^ n) =
      x / Real.log x ^ n + 2 ^ n * x / Real.log x ^ n := by ring
  linarith

/-- A constant is `O(x / log ^ k x)` at infinity for every `k : ℕ`. -/
private theorem isBigO_const_div_log_pow (c : ℝ) (k : ℕ) :
    (fun _ : ℝ ↦ c) =O[atTop] fun x : ℝ ↦ x / Real.log x ^ k := by
  have hlo := (_root_.isLittleO_log_rpow_rpow_atTop (k : ℝ) one_pos).bound one_pos
  refine IsBigO.of_bound |c| ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ), hlo] with x hx hbound
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_natCast, Real.rpow_one,
    abs_of_pos (pow_pos hlogx k), abs_of_pos hx0, one_mul] at hbound
  have h1 : 1 ≤ x / Real.log x ^ k := (one_le_div (pow_pos hlogx k)).mpr hbound
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (div_pos hx0 (pow_pos hlogx k))]
  exact le_mul_of_one_le_right (abs_nonneg c) h1

/-- **Asymptotic expansion of `Li`**: for every `n : ℕ`,
`Li x = (x / log x) ∑_{k < n} k! / (log x) ^ k + O(x / (log x) ^ (n + 1))`. -/
theorem logIntegral_sub_sum_isBigO (n : ℕ) :
    (fun x : ℝ ↦ logIntegral x -
      (x / Real.log x) * ∑ k ∈ Finset.range n, (k ! : ℝ) / Real.log x ^ k) =O[atTop]
      fun x : ℝ ↦ x / Real.log x ^ (n + 1) := by
  set c : ℝ := -(2 / Real.log 2) * ∑ k ∈ Finset.range n, (k ! : ℝ) / Real.log 2 ^ k
  have hsum : (fun x : ℝ ↦ c + (n ! : ℝ) * ∫ t in (2 : ℝ)..x, (Real.log t ^ (n + 1))⁻¹)
      =O[atTop] fun x : ℝ ↦ x / Real.log x ^ (n + 1) :=
    (isBigO_const_div_log_pow c (n + 1)).add
      ((integral_inv_log_pow_isBigO (n + 1)).const_mul_left (n ! : ℝ))
  refine hsum.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have h := logIntegral_eq_sum_add_integral n hx
  linarith

/-- **Asymptotic expansion of `li`**: for every `n : ℕ`,
`li x = (x / log x) ∑_{k < n} k! / (log x) ^ k + O(x / (log x) ^ (n + 1))`. -/
theorem principalLogIntegral_sub_sum_isBigO (n : ℕ) :
    (fun x : ℝ ↦ principalLogIntegral x -
      (x / Real.log x) * ∑ k ∈ Finset.range n, (k ! : ℝ) / Real.log x ^ k) =O[atTop]
      fun x : ℝ ↦ x / Real.log x ^ (n + 1) := by
  have h := (logIntegral_sub_sum_isBigO n).add
    (isBigO_const_div_log_pow (principalLogIntegral 2) (n + 1))
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hoff := principalLogIntegral_eq_logIntegral_add hx
  linarith

/-- `li x ~ Li x` as `x → ∞`. -/
theorem principalLogIntegral_isEquivalent_logIntegral :
    principalLogIntegral ~[atTop] logIntegral := by
  rw [IsEquivalent]
  have hconst : (fun _ : ℝ ↦ principalLogIntegral 2) =o[atTop] logIntegral :=
    (isLittleO_const_div_log (principalLogIntegral 2)).trans_isEquivalent
      logIntegral_isEquivalent_div_log.symm
  refine hconst.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  simp only [Pi.sub_apply]
  linarith [principalLogIntegral_eq_logIntegral_add hx]

/-- `li x ~ x / log x` as `x → ∞`. -/
theorem principalLogIntegral_isEquivalent_div_log :
    principalLogIntegral ~[atTop] fun x : ℝ ↦ x / Real.log x :=
  principalLogIntegral_isEquivalent_logIntegral.trans logIntegral_isEquivalent_div_log

/-! ### Series truncation helpers and numerical enclosures of `li` -/

/-- Monotonicity of `∑_{n ≥ 1} y ^ n / (n · n!)` for `0 ≤ y₁ ≤ y₂`. -/
private theorem tsum_pow_div_mul_factorial_mono {y₁ y₂ : ℝ} (hy₁ : 0 ≤ y₁) (h : y₁ ≤ y₂) :
    (∑' n : ℕ, y₁ ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) ≤
      ∑' n : ℕ, y₂ ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) :=
  (summable_pow_div_mul_factorial y₁).tsum_le_tsum
    (fun n ↦ div_le_div_of_nonneg_right (pow_le_pow_left₀ hy₁ h _) (by positivity))
    (summable_pow_div_mul_factorial y₂)

/-- Lower bound for `∑_{n ≥ 1} y ^ n / (n · n!)` by its `N`-th partial sum (`y ≥ 0`). -/
private theorem sum_range_le_tsum_pow_div_mul_factorial {y : ℝ} (hy : 0 ≤ y) (N : ℕ) :
    (∑ n ∈ Finset.range N, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) ≤
      ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) :=
  (summable_pow_div_mul_factorial y).sum_le_tsum (Finset.range N) fun _ _ ↦ by positivity

/-- One-step ratio bound for the terms of `∑_{n ≥ 1} y ^ n / (n · n!)`. -/
private theorem pow_div_mul_factorial_tail_le {y : ℝ} (hy : 0 ≤ y) (N m : ℕ) :
    y ^ (N + m + 1) / ((((N + m : ℕ) : ℝ) + 1) * ((N + m + 1)! : ℝ)) ≤
      y ^ (N + 1) / (((N : ℝ) + 1) * ((N + 1)! : ℝ)) * (y / ((N : ℝ) + 2)) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hfac : (((N + m + 1) + 1)! : ℝ) = ((N + m + 2 : ℝ)) * ((N + m + 1)! : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have h1 : (0 : ℝ) < ((N + m : ℝ) + 1) := by positivity
    have h2 : (0 : ℝ) < ((N + m : ℝ) + 2) := by positivity
    have h3 : (0 : ℝ) < ((N : ℝ) + 2) := by positivity
    have h4 : (0 : ℝ) < ((N + m + 1)! : ℝ) := by positivity
    have hle1 : ((N + m : ℝ) + 1) / ((N + m : ℝ) + 2) ≤ 1 := (div_le_one h2).mpr (by linarith)
    have hle2 : y / ((N + m : ℝ) + 2) ≤ y / ((N : ℝ) + 2) :=
      div_le_div_of_nonneg_left hy h3 (by linarith [Nat.cast_nonneg (α := ℝ) m])
    have heq : y ^ (N + (m + 1) + 1) /
        ((((N + (m + 1) : ℕ) : ℝ) + 1) * ((N + (m + 1) + 1)! : ℝ)) =
        (y ^ (N + m + 1) / ((((N + m : ℕ) : ℝ) + 1) * ((N + m + 1)! : ℝ))) *
          ((((N + m : ℝ) + 1) / ((N + m : ℝ) + 2)) * (y / ((N + m : ℝ) + 2))) := by
      have hadd : N + (m + 1) + 1 = (N + m + 1) + 1 := by omega
      rw [hadd, pow_succ, hfac]
      push_cast
      field_simp [h1.ne', h2.ne', h4.ne']
      ring
    rw [heq]
    calc _ ≤ (y ^ (N + m + 1) / ((((N + m : ℕ) : ℝ) + 1) * ((N + m + 1)! : ℝ))) *
          (1 * (y / ((N : ℝ) + 2))) := by gcongr
      _ = (y ^ (N + m + 1) / ((((N + m : ℕ) : ℝ) + 1) * ((N + m + 1)! : ℝ))) *
          (y / ((N : ℝ) + 2)) := by rw [one_mul]
      _ ≤ (y ^ (N + 1) / (((N : ℝ) + 1) * ((N + 1)! : ℝ)) * (y / ((N : ℝ) + 2)) ^ m) *
          (y / ((N : ℝ) + 2)) := mul_le_mul_of_nonneg_right ih (by positivity)
      _ = y ^ (N + 1) / (((N : ℝ) + 1) * ((N + 1)! : ℝ)) * (y / ((N : ℝ) + 2)) ^ (m + 1) := by
          ring

/-- Geometric tail bound for `∑_{n ≥ 1} y ^ n / (n · n!)` when `0 ≤ y < N + 2`. -/
private theorem tsum_pow_div_mul_factorial_le {y : ℝ} (hy : 0 ≤ y) {N : ℕ}
    (hyN : y < (N : ℝ) + 2) :
    (∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) ≤
      (∑ n ∈ Finset.range N, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) +
        y ^ (N + 1) / (((N : ℝ) + 1) * ((N + 1)! : ℝ)) * (((N : ℝ) + 2) / ((N : ℝ) + 2 - y)) := by
  let a : ℕ → ℝ := fun n ↦ y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))
  let r : ℝ := y / ((N : ℝ) + 2)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := (div_lt_one (by positivity)).mpr hyN
  have hsplit : (∑ n ∈ Finset.range N, a n) + (∑' m : ℕ, a (m + N)) = ∑' n : ℕ, a n :=
    (summable_pow_div_mul_factorial y).sum_add_tsum_nat_add N
  have htail_sum : Summable fun m : ℕ ↦ a (m + N) :=
    (summable_pow_div_mul_factorial y).comp_injective (add_left_injective N)
  have hgeom : Summable fun m : ℕ ↦ a N * r ^ m :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left (a N)
  have htail : (∑' m : ℕ, a (m + N)) ≤ a N * (((N : ℝ) + 2) / ((N : ℝ) + 2 - y)) := by
    calc (∑' m : ℕ, a (m + N)) ≤ ∑' m : ℕ, a N * r ^ m :=
          htail_sum.tsum_le_tsum (fun m ↦ by
            simp only [a, r, add_comm m N]
            exact pow_div_mul_factorial_tail_le hy N m) hgeom
      _ = a N * (1 - r)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
      _ = a N * (((N : ℝ) + 2) / ((N : ℝ) + 2 - y)) := by
          congr 1
          simp only [r]
          have hN2 : (0 : ℝ) < (N : ℝ) + 2 := by positivity
          have hsub : (0 : ℝ) < (N : ℝ) + 2 - y := by linarith
          field_simp [hN2.ne', hsub.ne']
  rw [← hsplit]
  exact add_le_add le_rfl htail

/-- Rational lower bound for `log x` via `Real.exp_bound` when `|a| ≤ 1`. -/
private theorem le_log_of_exp_bound {a x : ℝ} (hx : 0 < x) (ha : |a| ≤ 1) {n : ℕ} (hn : 0 < n)
    (h : (∑ m ∈ Finset.range n, a ^ m / (m ! : ℝ)) +
      |a| ^ n * (((n : ℝ) + 1) / ((n ! : ℝ) * (n : ℝ))) ≤ x) :
    a ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le hx]
  have hb := (abs_le.mp (Real.exp_bound ha hn)).2
  rw [Nat.cast_succ] at hb
  linarith

/-- Rational upper bound for `log x` via `Real.exp_bound` when `|b| ≤ 1`. -/
private theorem log_le_of_exp_bound {b x : ℝ} (hx : 0 < x) (hb : |b| ≤ 1) {n : ℕ} (hn : 0 < n)
    (h : x ≤ (∑ m ∈ Finset.range n, b ^ m / (m ! : ℝ)) -
      |b| ^ n * (((n : ℝ) + 1) / ((n ! : ℝ) * (n : ℝ)))) :
    Real.log x ≤ b := by
  rw [Real.log_le_iff_le_exp hx]
  have hlow := (abs_le.mp (Real.exp_bound hb hn)).1
  rw [Nat.cast_succ] at hlow
  linarith

/-- `li x > 0` for every `x ≥ 3 / 2`. -/
theorem principalLogIntegral_pos_of_three_halves_le {x : ℝ} (hx : 3 / 2 ≤ x) :
    0 < principalLogIntegral x := by
  have hlog32 : (0.4054 : ℝ) ≤ Real.log (3 / 2) := by
    refine le_log_of_exp_bound (by norm_num) (by norm_num) (n := 6) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hloglog : (-0.903 : ℝ) ≤ Real.log (Real.log (3 / 2)) := by
    refine le_trans ?_ (Real.log_le_log (by norm_num) hlog32)
    refine le_log_of_exp_bound (by norm_num) (by norm_num) (n := 8) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hser : (0.446 : ℝ) ≤
      ∑' n : ℕ, Real.log (3 / 2) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
    have hnum : (0.446 : ℝ) ≤
        ∑ n ∈ Finset.range 2, (0.4054 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact hnum.trans ((sum_range_le_tsum_pow_div_mul_factorial (y := (0.4054 : ℝ))
      (by norm_num) 2).trans (tsum_pow_div_mul_factorial_mono (by norm_num) hlog32))
  have h32 : 0 < principalLogIntegral (3 / 2) := by
    rw [principalLogIntegral_def]
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  rcases hx.eq_or_lt with rfl | hlt
  · exact h32
  · exact h32.trans (strictMonoOn_principalLogIntegral (by norm_num)
      (mem_Ioi.mpr (by linarith)) hlt)

/-- Unconditional lower bound `0.83446 ≤ ∑_{n ≥ 1} (log 2) ^ n / (n · n!)`. -/
theorem tsum_log_two_pow_div_ge :
    (0.83446 : ℝ) ≤ ∑' n : ℕ, Real.log 2 ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
  have hlog2 : (0.693147 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hnum : (0.83446 : ℝ) ≤
      ∑ n ∈ Finset.range 7, (0.693147 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact hnum.trans ((sum_range_le_tsum_pow_div_mul_factorial (y := (0.693147 : ℝ))
    (by norm_num) 7).trans (tsum_pow_div_mul_factorial_mono (by norm_num) hlog2))

/-- Unconditional upper bound `∑_{n ≥ 1} (log 2) ^ n / (n · n!) ≤ 0.834462`. -/
theorem tsum_log_two_pow_div_le :
    (∑' n : ℕ, Real.log 2 ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) ≤ 0.834462 := by
  have hlog2 : Real.log 2 ≤ (0.6931472 : ℝ) := by linarith [Real.log_two_lt_d9]
  have h1 := (tsum_pow_div_mul_factorial_mono (Real.log_pos one_lt_two).le hlog2).trans
    (tsum_pow_div_mul_factorial_le (y := (0.6931472 : ℝ)) (by norm_num) (N := 7) (by norm_num))
  have hnum : (∑ n ∈ Finset.range 7, (0.6931472 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) +
      (0.6931472 : ℝ) ^ (7 + 1) / ((((7 : ℕ) : ℝ) + 1) * ((7 + 1)! : ℝ)) *
        ((((7 : ℕ) : ℝ) + 2) / (((7 : ℕ) : ℝ) + 2 - 0.6931472)) ≤ 0.834462 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact h1.trans hnum

/-- Unconditional lower bound `-0.366513 ≤ log (log 2)`. -/
theorem log_log_two_ge : (-0.366513 : ℝ) ≤ Real.log (Real.log 2) := by
  have h1 : (-0.366513 : ℝ) ≤ Real.log (0.6931471803 : ℝ) := by
    refine le_log_of_exp_bound (by norm_num) (by norm_num) (n := 8) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact h1.trans (Real.log_le_log (by norm_num) Real.log_two_gt_d9.le)

/-- Unconditional upper bound `log (log 2) ≤ -0.366512`. -/
theorem log_log_two_le : Real.log (Real.log 2) ≤ -0.366512 := by
  have h1 : Real.log (0.6931471808 : ℝ) ≤ (-0.366512 : ℝ) := by
    refine log_le_of_exp_bound (by norm_num) (by norm_num) (n := 8) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact (Real.log_le_log (Real.log_pos one_lt_two) Real.log_two_lt_d9.le).trans h1

/-- Unconditional lower bound `0.467947 ≤ li 2 - γ`. -/
theorem principalLogIntegral_two_sub_eulerGamma_ge :
    (0.467947 : ℝ) ≤ principalLogIntegral 2 - Real.eulerMascheroniConstant := by
  rw [principalLogIntegral_def]
  linarith [log_log_two_ge, tsum_log_two_pow_div_ge]

/-- Unconditional upper bound `li 2 - γ ≤ 0.46795`. -/
theorem principalLogIntegral_two_sub_eulerGamma_le :
    principalLogIntegral 2 - Real.eulerMascheroniConstant ≤ 0.46795 := by
  rw [principalLogIntegral_def]
  linarith [log_log_two_le, tsum_log_two_pow_div_le]

/-- Unconditional lower bound `0.96 < li 2`. -/
theorem principalLogIntegral_two_gt : (0.96 : ℝ) < principalLogIntegral 2 := by
  linarith [Real.one_half_lt_eulerMascheroniConstant, principalLogIntegral_two_sub_eulerGamma_ge]

/-- Unconditional upper bound `li 2 < 1.14`. -/
theorem principalLogIntegral_two_lt : principalLogIntegral 2 < 1.14 := by
  linarith [Real.eulerMascheroniConstant_lt_two_thirds, principalLogIntegral_two_sub_eulerGamma_le]

/-- `li 2 > 0`. -/
theorem principalLogIntegral_two_pos : 0 < principalLogIntegral 2 :=
  lt_trans (by norm_num) principalLogIntegral_two_gt

/-- The unoffset and offset logarithmic integrals are distinct (`li 2 > 0` while `Li 2 = 0`). -/
theorem principalLogIntegral_ne_logIntegral : principalLogIntegral ≠ logIntegral := by
  intro h
  have h2 := congr_fun h 2
  rw [logIntegral_two] at h2
  exact principalLogIntegral_two_pos.ne' h2

/-- Conditional lower bound `1.0451 ≤ li 2` from a `10⁻⁹` enclosure of `γ`. -/
theorem principalLogIntegral_two_ge_of_eulerGamma
    (hγ : |Real.eulerMascheroniConstant - 0.5772156649| ≤ (10 : ℝ) ^ (-9 : ℤ)) :
    (1.0451 : ℝ) ≤ principalLogIntegral 2 := by
  have hγ_lo := (abs_le.mp hγ).1
  norm_num at hγ_lo
  linarith [principalLogIntegral_two_sub_eulerGamma_ge]

/-- Conditional upper bound `li 2 ≤ 1.0452` from a `10⁻⁹` enclosure of `γ`. -/
theorem principalLogIntegral_two_le_of_eulerGamma
    (hγ : |Real.eulerMascheroniConstant - 0.5772156649| ≤ (10 : ℝ) ^ (-9 : ℤ)) :
    principalLogIntegral 2 ≤ 1.0452 := by
  have hγ_hi := (abs_le.mp hγ).2
  norm_num at hγ_hi
  linarith [principalLogIntegral_two_sub_eulerGamma_le]

/-! ### Comparison of `Li x` with `x / log x` -/

/-- The derivative of `x ↦ Li x - x / log x` on `(1, ∞)` is `(log x ^ 2)⁻¹`. -/
theorem hasDerivAt_logIntegral_sub_div_log {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun t : ℝ ↦ logIntegral t - t / Real.log t) (Real.log x ^ 2)⁻¹ x := by
  have hd1 := hasDerivAt_logIntegral hx
  have hd2 : HasDerivAt (fun t : ℝ ↦ t / Real.log t)
      ((Real.log x)⁻¹ - (Real.log x ^ 2)⁻¹) x := by
    simpa only [pow_one, Nat.cast_one, one_mul] using hasDerivAt_div_log_pow 1 (Real.log_pos hx).ne'
  exact (hd1.sub hd2).congr_deriv (by ring)

/-- `x ↦ Li x - x / log x` is strictly increasing on `(1, ∞)`. -/
theorem strictMonoOn_logIntegral_sub_div_log :
    StrictMonoOn (fun t : ℝ ↦ logIntegral t - t / Real.log t) (Ioi 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 1) ?_ fun x hx ↦ ?_
  · exact fun t ht ↦ (hasDerivAt_logIntegral_sub_div_log ht).continuousAt.continuousWithinAt
  · rw [interior_Ioi] at hx
    rw [(hasDerivAt_logIntegral_sub_div_log hx).deriv]
    exact inv_pos.mpr (pow_pos (Real.log_pos hx) 2)

/-- Lower bound `x / log² x - 2 / log 2 - 2 / log² 2 ≤ Li x - x / log x` for `x ≥ 2`
(with equality at `x = 2`). -/
theorem le_logIntegral_sub_div_log {x : ℝ} (hx : 2 ≤ x) :
    x / Real.log x ^ 2 - 2 / Real.log 2 - 2 / Real.log 2 ^ 2 ≤
      logIntegral x - x / Real.log x := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogx : Real.log 2 ≤ Real.log x := Real.log_le_log two_pos hx
  have hle1 : (x - 2) / Real.log x ^ 2 ≤ ∫ t in (2 : ℝ)..x, (Real.log t ^ 2)⁻¹ :=
    le_integral_inv_log_pow 2 one_lt_two hx
  have hle2 : 2 / Real.log x ^ 2 ≤ 2 / Real.log 2 ^ 2 :=
    div_le_div_of_nonneg_left zero_le_two (pow_pos hlog2 2) (pow_le_pow_left₀ hlog2.le hlogx 2)
  have hid := logIntegral_eq_div_log_sub_add hx
  rw [sub_div] at hle1
  linarith

/-- Strict lower bound `x / log² x - 2 / log 2 - 2 / log² 2 < Li x - x / log x` for `x > 2`. -/
theorem lt_logIntegral_sub_div_log {x : ℝ} (hx : 2 < x) :
    x / Real.log x ^ 2 - 2 / Real.log 2 - 2 / Real.log 2 ^ 2 <
      logIntegral x - x / Real.log x := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogx : Real.log 2 < Real.log x := Real.log_lt_log two_pos hx
  have hle1 : (x - 2) / Real.log x ^ 2 ≤ ∫ t in (2 : ℝ)..x, (Real.log t ^ 2)⁻¹ :=
    le_integral_inv_log_pow 2 one_lt_two hx.le
  have hlt2 : 2 / Real.log x ^ 2 < 2 / Real.log 2 ^ 2 :=
    div_lt_div_of_pos_left two_pos (pow_pos hlog2 2)
      (pow_lt_pow_left₀ hlogx hlog2.le (by norm_num))
  have hid := logIntegral_eq_div_log_sub_add hx.le
  rw [sub_div] at hle1
  linarith

/-- Upper bound `Li x - x / log x < x / log² x + 2 √x / log³ 2 + 16 x / log³ x - 2 / log 2` for
every `x > 1`. -/
theorem logIntegral_sub_div_log_lt {x : ℝ} (hx : 1 < x) :
    logIntegral x - x / Real.log x <
      x / Real.log x ^ 2 + 2 * √x / Real.log 2 ^ 3 + 16 * x / Real.log x ^ 3 - 2 / Real.log 2 := by
  have h := integral_inv_log_pow_lt 2 hx
  have hid : logIntegral x = x / Real.log x - 2 / Real.log 2 +
      ∫ t in (2 : ℝ)..x, (Real.log t ^ 2)⁻¹ := by
    rw [logIntegral_def]
    simpa only [pow_one, Nat.cast_one, one_mul] using
      integral_inv_log_pow_eq_sub_add 1 one_lt_two hx
  have hring : x / Real.log x ^ 2 + (2 : ℝ) * (√x / Real.log 2 ^ 3 + 2 ^ 3 * x / Real.log x ^ 3) =
      x / Real.log x ^ 2 + 2 * √x / Real.log 2 ^ 3 + 16 * x / Real.log x ^ 3 := by ring
  norm_num at h
  linarith

/-- `Li 6.5797 < 6.5797 / log 6.5797`, proved via the `li` series where `γ` cancels. -/
private theorem logIntegral_sub_div_log_neg_at :
    logIntegral 6.5797 - 6.5797 / Real.log 6.5797 < 0 := by
  have hlog_le : Real.log 6.5797 ≤ (1.88399 : ℝ) := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have hsq : Real.exp (1.88399 : ℝ) = Real.exp (0.941995 : ℝ) ^ 2 := by
      rw [sq, ← Real.exp_add]; norm_num
    have hb := (abs_le.mp (Real.exp_bound (x := (0.941995 : ℝ)) (by norm_num) (n := 10)
      (by norm_num))).1
    norm_num [Finset.sum_range_succ, Nat.factorial] at hb
    rw [hsq]
    nlinarith
  have hlog_pos : 0 < Real.log 6.5797 := Real.log_pos (by norm_num)
  have hll_le : Real.log (Real.log 6.5797) ≤ (0.633392 : ℝ) := by
    refine (Real.log_le_log hlog_pos hlog_le).trans ?_
    refine log_le_of_exp_bound (by norm_num) (by norm_num) (n := 9) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hser_le : (∑' n : ℕ, Real.log 6.5797 ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) ≤
      3.326982 := by
    have h1 := (tsum_pow_div_mul_factorial_mono hlog_pos.le hlog_le).trans
      (tsum_pow_div_mul_factorial_le (y := (1.88399 : ℝ)) (by norm_num) (N := 10) (by norm_num))
    have hnum :
        (∑ n ∈ Finset.range 10, (1.88399 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) +
        (1.88399 : ℝ) ^ (10 + 1) / ((((10 : ℕ) : ℝ) + 1) * ((10 + 1)! : ℝ)) *
          ((((10 : ℕ) : ℝ) + 2) / (((10 : ℕ) : ℝ) + 2 - 1.88399)) ≤ 3.326982 := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact h1.trans hnum
  have hdiv_ge : (6.5797 : ℝ) / 1.88399 ≤ 6.5797 / Real.log 6.5797 :=
    div_le_div_of_nonneg_left (by norm_num) hlog_pos hlog_le
  rw [logIntegral_eq_principalLogIntegral_sub (by norm_num),
    principalLogIntegral_def, principalLogIntegral_def]
  linarith [log_log_two_ge, tsum_log_two_pow_div_ge]

/-- `6.5798 / log 6.5798 < Li 6.5798`, proved via the `li` series where `γ` cancels. -/
private theorem logIntegral_sub_div_log_pos_at :
    0 < logIntegral 6.5798 - 6.5798 / Real.log 6.5798 := by
  have hlog_ge : (1.884003 : ℝ) ≤ Real.log 6.5798 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have hsq : Real.exp (1.884003 : ℝ) = Real.exp (0.9420015 : ℝ) ^ 2 := by
      rw [sq, ← Real.exp_add]; norm_num
    have hb := (abs_le.mp (Real.exp_bound (x := (0.9420015 : ℝ)) (by norm_num) (n := 9)
      (by norm_num))).2
    norm_num [Finset.sum_range_succ, Nat.factorial] at hb
    rw [hsq]
    nlinarith [Real.exp_pos (0.9420015 : ℝ)]
  have hll_ge : (0.633398 : ℝ) ≤ Real.log (Real.log 6.5798) := by
    refine le_trans ?_ (Real.log_le_log (by norm_num) hlog_ge)
    refine le_log_of_exp_bound (by norm_num) (by norm_num) (n := 8) (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hser_ge : (3.32701 : ℝ) ≤
      ∑' n : ℕ, Real.log 6.5798 ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
    have hnum : (3.32701 : ℝ) ≤
        ∑ n ∈ Finset.range 10, (1.884003 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    exact hnum.trans ((sum_range_le_tsum_pow_div_mul_factorial (y := (1.884003 : ℝ))
      (by norm_num) 10).trans (tsum_pow_div_mul_factorial_mono (by norm_num) hlog_ge))
  have hdiv_le : 6.5798 / Real.log 6.5798 ≤ (6.5798 : ℝ) / 1.884003 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlog_ge
  rw [logIntegral_eq_principalLogIntegral_sub (by norm_num),
    principalLogIntegral_def, principalLogIntegral_def]
  linarith [log_log_two_le, tsum_log_two_pow_div_le]

/-- `Li x = x / log x` has a unique solution in `(6.5797, 6.5798)`. -/
theorem existsUnique_logIntegral_eq_div_log_Ioo :
    ∃! x ∈ Ioo (6.5797 : ℝ) 6.5798, logIntegral x = x / Real.log x := by
  have hcont : ContinuousOn (fun t : ℝ ↦ logIntegral t - t / Real.log t) (Icc 6.5797 6.5798) :=
    fun t ht ↦ (hasDerivAt_logIntegral_sub_div_log
      (by linarith [ht.1])).continuousAt.continuousWithinAt
  obtain ⟨x₀, hx₀, hfx₀⟩ := intermediate_value_Icc (by norm_num : (6.5797 : ℝ) ≤ 6.5798) hcont
    ⟨logIntegral_sub_div_log_neg_at.le, logIntegral_sub_div_log_pos_at.le⟩
  have hlt1 : 6.5797 < x₀ := lt_of_le_of_ne hx₀.1 fun h ↦ by
    subst h; linarith [logIntegral_sub_div_log_neg_at]
  have hlt2 : x₀ < 6.5798 := lt_of_le_of_ne hx₀.2 fun h ↦ by
    subst h; linarith [logIntegral_sub_div_log_pos_at]
  refine ⟨x₀, ⟨⟨hlt1, hlt2⟩, sub_eq_zero.mp hfx₀⟩, fun y ⟨hy, hfy⟩ ↦ ?_⟩
  exact strictMonoOn_logIntegral_sub_div_log.injOn (mem_Ioi.mpr (by linarith [hy.1]))
    (mem_Ioi.mpr (by linarith)) (by linarith [hfy, hfx₀])

/-- `Li x = x / log x` has a unique solution on `(1, ∞)`. -/
theorem existsUnique_logIntegral_eq_div_log :
    ∃! x ∈ Ioi (1 : ℝ), logIntegral x = x / Real.log x := by
  obtain ⟨x₀, ⟨hx₀, hfx₀⟩, _⟩ := existsUnique_logIntegral_eq_div_log_Ioo
  refine ⟨x₀, ⟨mem_Ioi.mpr (by linarith [hx₀.1]), hfx₀⟩, fun y ⟨hy, hfy⟩ ↦ ?_⟩
  exact strictMonoOn_logIntegral_sub_div_log.injOn hy (mem_Ioi.mpr (by linarith [hx₀.1]))
    (by rw [hfy, hfx₀, sub_self, sub_self])

/-- **Fiori–Kadiri–Swidinsky lower bound**: for every `x > 1`,
`(x - 6.58) / (log x) ^ 2 < Li x - x / log x`. -/
theorem sub_div_log_sq_lt_logIntegral_sub_div_log {x : ℝ} (hx : 1 < x) :
    (x - 6.58) / Real.log x ^ 2 < logIntegral x - x / Real.log x := by
  have hpos : 0 < logIntegral 6.58 - 6.58 / Real.log 6.58 :=
    logIntegral_sub_div_log_pos_at.trans
      (strictMonoOn_logIntegral_sub_div_log (by norm_num) (by norm_num) (by norm_num))
  have hFTC : (logIntegral x - x / Real.log x) - (logIntegral 6.58 - 6.58 / Real.log 6.58) =
      ∫ t in (6.58 : ℝ)..x, (Real.log t ^ 2)⁻¹ := by
    refine (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ ↦ logIntegral t - t / Real.log t) (fun t ht ↦ ?_) ?_).symm
    · rcases mem_uIcc.mp ht with h | h
      · exact hasDerivAt_logIntegral_sub_div_log (by linarith [h.1])
      · exact hasDerivAt_logIntegral_sub_div_log (hx.trans_le h.1)
    · exact intervalIntegrable_inv_log_pow 2 (by norm_num) hx
  rcases le_or_gt (6.58 : ℝ) x with hge | hlt
  · have hint := le_integral_inv_log_pow 2 (by norm_num : (1 : ℝ) < 6.58) hge
    linarith
  · have hint := integral_inv_log_pow_le 2 hx hlt.le
    rw [intervalIntegral.integral_symm x 6.58] at hFTC
    have hneg : -((6.58 - x) / Real.log x ^ 2) = (x - 6.58) / Real.log x ^ 2 := by ring
    linarith

/-- For every `x ≥ 6.58`, `x / log x < Li x`. -/
theorem div_log_lt_logIntegral {x : ℝ} (hx : 6.58 ≤ x) : x / Real.log x < logIntegral x := by
  have h := sub_div_log_sq_lt_logIntegral_sub_div_log (by linarith : (1 : ℝ) < x)
  have hnn : 0 ≤ (x - 6.58) / Real.log x ^ 2 := div_nonneg (by linarith) (sq_nonneg _)
  linarith

end TauCeti.Real
