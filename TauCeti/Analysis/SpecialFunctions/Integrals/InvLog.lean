/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.SpecialFunctions.Log.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Analysis.SpecialFunctions.Log.InvLog

/-!
# Integrals of reciprocal logarithms and their powers

This file establishes continuity, interval integrability, monotonicity bounds, integration by parts,
explicit remainder estimates, and asymptotics for reciprocal powers `(log t ^ k)⁻¹` and
`(log t ^ n)⁻¹`, weighted integrals against `(t * log t ^ 2)⁻¹`, as well as interval
integrability of `(log t)⁻¹` on `[0, 1)`, the pole-subtracted integrand `(log t)⁻¹ - (t - 1)⁻¹`
on `[0, ∞)`, and the symmetrically folded integrand `(log (1 + u))⁻¹ + (log (1 - u))⁻¹` on
`[0, 1]`.

Separating these integrand and integral lemmas from `TauCeti.Analysis.SpecialFunctions.LogIntegral`
lets consumers of reciprocal-log integrals (such as Abel summation and regularization estimates)
import them directly without depending on `Li`, `li`, or `Real.eulerMascheroniConstant`.

## Main declarations

* `Real.continuousOn_inv_log_rpow`, `Real.intervalIntegrable_inv_log_rpow`,
  `Real.integral_inv_log_rpow_le`, `Real.le_integral_inv_log_rpow`,
  `Real.integral_inv_log_rpow_nonneg`, `Real.integral_inv_log_rpow_eq_sub_add` — continuity,
  monotonicity bounds, and integration by parts for reciprocal real powers `(log t ^ k)⁻¹` on
  intervals with `a, b > 1`.
* `Real.integral_inv_log_rpow_le_sqrt_add`, `Real.integral_inv_log_rpow_lt_div_add`,
  `Real.integral_inv_log_pow_le_sqrt_add`, `Real.integral_inv_log_pow_lt_div_add`,
  `Real.isBigO_integral_inv_log_pow` — explicit upper bounds and `O(x / log x ^ n)` remainder
  estimate for `∫ t in 2..x, (log t ^ k)⁻¹`.
* `TauCeti.Real.continuousOn_inv_log_pow`, `TauCeti.Real.continuousOn_inv_div_log_pow`,
  `TauCeti.Real.intervalIntegrable_inv_log_pow`, `TauCeti.Real.integral_inv_log_pow_le`,
  `TauCeti.Real.le_integral_inv_log_pow`, `TauCeti.Real.integral_inv_log_pow_nonneg`,
  `TauCeti.Real.integral_inv_log_pow_eq_sub_add` — natural-exponent specializations.
* `TauCeti.Real.isLittleO_integral_inv_log_sq`,
  `TauCeti.Real.tendsto_integral_inv_log_sq_mul_log_div_atTop` — the square-remainder
  `o(x / log x)` asymptotic and quotient limit.
* `TauCeti.Real.intervalIntegrable_div_mul_log_sq`, `TauCeti.Real.intervalIntegrable_div_log_sq`,
  `TauCeti.Real.integral_div_mul_log_sq_eq_sub_add`,
  `TauCeti.Real.integral_div_mul_log_sq_le_integral_div_log_sq`,
  `TauCeti.Real.neg_integral_div_log_sq_le_integral_div_mul_log_sq`,
  `TauCeti.Real.abs_integral_div_mul_log_sq_le_integral_div_log_sq`,
  `TauCeti.Real.abs_integral_div_mul_log_sq_le_add`,
  `TauCeti.Real.isLittleO_integral_div_mul_log_sq` — weighted reciprocal-log integrability,
  comparisons, quantitative cutoff bound, and `o(x / log x)` estimate.
* `Real.intervalIntegrable_inv_log_of_lt_one` — interval integrability of `(log t)⁻¹` on `[0, 1)`.
* `Real.intervalIntegrable_inv_log_sub_inv_sub_one`,
  `Real.intervalIntegrable_inv_log_one_add_sub_inv`,
  `Real.intervalIntegrable_inv_log_one_sub_add_inv`,
  `Real.intervalIntegrable_inv_log_one_add_add_inv_log_one_sub` — interval integrability of the
  pole-subtracted and symmetrically folded integrands.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapters 7 and 18.
* The integration-by-parts recurrence is adapted from the Ramanujan estimates in the
  [PrimeNumberTheoremAnd project](https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/dc6e36e/PrimeNumberTheoremAnd/IEANTN/Ramanujan/Ramanujan.lean).
-/

public section

open Asymptotics Filter MeasureTheory Set
open scoped Topology

namespace Real

/-! ### Reciprocal real powers of the logarithm -/

/-- Reciprocal real powers of `log` are continuous on `(1, ∞)`. -/
theorem continuousOn_inv_log_rpow (k : ℝ) :
    ContinuousOn (fun t : ℝ ↦ (log t ^ k)⁻¹) (Ioi 1) := by
  have hlog : ContinuousOn log (Ioi 1) :=
    continuousOn_log.mono fun t ht ↦ ne_of_gt (zero_lt_one.trans ht)
  have hrpow : ContinuousOn (fun t : ℝ ↦ log t ^ k) (Ioi 1) :=
    hlog.rpow_const fun t ht ↦ Or.inl (log_pos ht).ne'
  exact hrpow.inv₀ fun t ht ↦ (rpow_pos_of_pos (log_pos ht) k).ne'

/-- Reciprocal real powers of `log` are interval integrable on any interval to the right of `1`. -/
theorem intervalIntegrable_inv_log_rpow (k : ℝ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t : ℝ ↦ (log t ^ k)⁻¹) volume a b := by
  refine ((continuousOn_inv_log_rpow k).mono fun t ht ↦ ?_).intervalIntegrable
  rcases mem_uIcc.mp ht with ht | ht
  · exact ha.trans_le ht.1
  · exact hb.trans_le ht.1

/-- Monotonicity upper bound `∫ t in a..b, (log t ^ k)⁻¹ ≤ (b - a) / log a ^ k` for `k ≥ 0`. -/
theorem integral_inv_log_rpow_le {k : ℝ} (hk : 0 ≤ k) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, (log t ^ k)⁻¹ ≤ (b - a) / log a ^ k := by
  have hla : 0 < log a := log_pos ha
  have hb : 1 < b := ha.trans_le hab
  have hmono := intervalIntegral.integral_mono_on hab (intervalIntegrable_inv_log_rpow k ha hb)
    (g := fun _ ↦ (log a ^ k)⁻¹) intervalIntegrable_const fun t ht ↦
      inv_anti₀ (rpow_pos_of_pos hla k)
        (rpow_le_rpow hla.le (log_le_log (by linarith) ht.1) hk)
  simpa [smul_eq_mul, div_eq_mul_inv] using hmono

/-- Monotonicity lower bound `(b - a) / log b ^ k ≤ ∫ t in a..b, (log t ^ k)⁻¹` for `k ≥ 0`. -/
theorem le_integral_inv_log_rpow {k : ℝ} (hk : 0 ≤ k) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (b - a) / log b ^ k ≤ ∫ t in a..b, (log t ^ k)⁻¹ := by
  have hb : 1 < b := ha.trans_le hab
  have hmono := intervalIntegral.integral_mono_on hab
    (f := fun _ ↦ (log b ^ k)⁻¹) intervalIntegrable_const
    (intervalIntegrable_inv_log_rpow k ha hb) fun t ht ↦ by
      have hlt : 0 < log t := log_pos (ha.trans_le ht.1)
      exact inv_anti₀ (rpow_pos_of_pos hlt k)
        (rpow_le_rpow hlt.le (log_le_log (zero_lt_one.trans (ha.trans_le ht.1)) ht.2) hk)
  simpa [smul_eq_mul, div_eq_mul_inv] using hmono

/-- The integrand `(log t ^ k)⁻¹` is nonnegative to the right of `1`, so its integral is. -/
theorem integral_inv_log_rpow_nonneg (k : ℝ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    0 ≤ ∫ t in a..b, (log t ^ k)⁻¹ :=
  intervalIntegral.integral_nonneg hab fun _ ht ↦
    inv_nonneg.mpr (rpow_pos_of_pos (log_pos (ha.trans_le ht.1)) k).le

/-- Integration by parts for `∫ t in a..b, (log t ^ k)⁻¹` with any real exponent `k` and
endpoints `a, b > 1`. -/
theorem integral_inv_log_rpow_eq_sub_add (k : ℝ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    (∫ t in a..b, (log t ^ k)⁻¹) =
      b / log b ^ k - a / log a ^ k + k * ∫ t in a..b, (log t ^ (k + 1))⁻¹ := by
  have hi := intervalIntegrable_inv_log_rpow k ha hb
  have hi1 := intervalIntegrable_inv_log_rpow (k + 1) ha hb
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hasDerivAt_div_log_rpow k (log_pos (by
      rcases mem_uIcc.mp ht with ht | ht
      · exact ha.trans_le ht.1
      · exact hb.trans_le ht.1)))
    (hi.sub (hi1.const_mul k))
  rw [intervalIntegral.integral_sub hi (hi1.const_mul k),
    intervalIntegral.integral_const_mul] at hFTC
  exact sub_eq_iff_eq_add.mp hFTC

/-- Explicit upper bound `∫ t in 2..x, (log t ^ k)⁻¹ ≤ √x / log 2 ^ k + 2 ^ k * x / log x ^ k`
for every real `k ≥ 0` and `x ≥ 2`. -/
theorem integral_inv_log_rpow_le_sqrt_add {k : ℝ} (hk : 0 ≤ k) {x : ℝ} (hx : 2 ≤ x) :
    (∫ t in (2 : ℝ)..x, (log t ^ k)⁻¹) ≤
      √x / log 2 ^ k + 2 ^ k * x / log x ^ k := by
  have hx0 : 0 < x := by linarith
  have hlog2 : 0 < log 2 := log_pos one_lt_two
  have hlogx : 0 < log x := log_pos (by linarith)
  rcases le_or_gt 4 x with h4 | h4
  · have hsq : 2 ≤ √x := by nlinarith [sq_sqrt hx0.le, sqrt_nonneg x]
    have hle : √x ≤ x := by
      rw [sqrt_le_self_iff]
      exact Or.inr (by linarith)
    have hsplit : (∫ t in (2 : ℝ)..x, (log t ^ k)⁻¹) =
        (∫ t in (2 : ℝ)..√x, (log t ^ k)⁻¹) + ∫ t in √x..x, (log t ^ k)⁻¹ :=
      (intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_inv_log_rpow k one_lt_two (by linarith))
        (intervalIntegrable_inv_log_rpow k (by linarith) (by linarith))).symm
    have hb₁ : (∫ t in (2 : ℝ)..√x, (log t ^ k)⁻¹) ≤ √x / log 2 ^ k := by
      refine (integral_inv_log_rpow_le hk one_lt_two hsq).trans ?_
      gcongr
      linarith
    have hb₂ : (∫ t in √x..x, (log t ^ k)⁻¹) ≤ 2 ^ k * x / log x ^ k := by
      refine (integral_inv_log_rpow_le hk (by linarith) hle).trans ?_
      rw [log_sqrt hx0.le, div_rpow hlogx.le zero_le_two, div_div_eq_mul_div, mul_comm (x - √x)]
      gcongr
      linarith [sqrt_nonneg x]
    rw [hsplit]
    linarith
  · have hlog_half : log x / 2 ≤ log 2 := by
      have h : log x ≤ log (2 ^ 2) := log_le_log hx0 (by norm_num; exact h4.le)
      rw [log_pow] at h
      norm_num at h
      linarith
    have hb : (∫ t in (2 : ℝ)..x, (log t ^ k)⁻¹) ≤ 2 ^ k * x / log x ^ k := by
      refine (integral_inv_log_rpow_le hk one_lt_two hx).trans ?_
      have hrpow_le : (log x / 2) ^ k ≤ log 2 ^ k := rpow_le_rpow (by positivity) hlog_half hk
      have hdiv : (x - 2) / log 2 ^ k ≤ (x - 2) / (log x / 2) ^ k :=
        div_le_div_of_nonneg_left (by linarith) (rpow_pos_of_pos (by positivity) k) hrpow_le
      refine hdiv.trans ?_
      rw [div_rpow hlogx.le zero_le_two, div_div_eq_mul_div, mul_comm (x - 2)]
      gcongr
      linarith
    have hnn : 0 ≤ √x / log 2 ^ k := div_nonneg (sqrt_nonneg x) (rpow_pos_of_pos hlog2 k).le
    linarith

/-- Explicit strict upper bound
`∫ t in 2..x, (log t ^ k)⁻¹ <`
`x / log x ^ k + k * (√x / log 2 ^ (k + 1) + 2 ^ (k + 1) * x / log x ^ (k + 1))`
for every real `k ≥ 0` and `x ≥ 2`. -/
theorem integral_inv_log_rpow_lt_div_add {k : ℝ} (hk : 0 ≤ k) {x : ℝ} (hx : 2 ≤ x) :
    (∫ t in (2 : ℝ)..x, (log t ^ k)⁻¹) <
      x / log x ^ k +
        k * (√x / log 2 ^ (k + 1) + 2 ^ (k + 1) * x / log x ^ (k + 1)) := by
  rw [integral_inv_log_rpow_eq_sub_add k one_lt_two (by linarith)]
  have h2pos : 0 < 2 / log 2 ^ k := div_pos two_pos (rpow_pos_of_pos (log_pos one_lt_two) k)
  have hrem := integral_inv_log_rpow_le_sqrt_add (k := k + 1) (by linarith) hx
  linarith [mul_le_mul_of_nonneg_left hrem hk]

/-- Explicit upper bound `∫ t in 2..x, (log t ^ n)⁻¹ ≤ √x / log 2 ^ n + 2 ^ n * x / log x ^ n`
for every `n : ℕ` and `x ≥ 2`. -/
theorem integral_inv_log_pow_le_sqrt_add (n : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    (∫ t in (2 : ℝ)..x, (log t ^ n)⁻¹) ≤
      √x / log 2 ^ n + 2 ^ n * x / log x ^ n := by
  simpa only [rpow_natCast] using
    integral_inv_log_rpow_le_sqrt_add (k := (n : ℝ)) (Nat.cast_nonneg n) hx

/-- Explicit strict upper bound
`∫ t in 2..x, (log t ^ n)⁻¹ <`
`x / log x ^ n + n * (√x / log 2 ^ (n + 1) + 2 ^ (n + 1) * x / log x ^ (n + 1))`
for every `n : ℕ` and `x ≥ 2`. -/
theorem integral_inv_log_pow_lt_div_add (n : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    (∫ t in (2 : ℝ)..x, (log t ^ n)⁻¹) <
      x / log x ^ n +
        (n : ℝ) * (√x / log 2 ^ (n + 1) + 2 ^ (n + 1) * x / log x ^ (n + 1)) := by
  have h := integral_inv_log_rpow_lt_div_add (k := (n : ℝ)) (Nat.cast_nonneg n) hx
  simpa only [rpow_natCast, ← Nat.cast_add_one] using h

/-! ### Ordinary, pole-subtracted, and symmetric reciprocal-log integrability -/

/-- `(log t)⁻¹` is interval integrable on any interval contained in `[0, 1)`. -/
theorem intervalIntegrable_inv_log_of_lt_one {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1) :
    IntervalIntegrable (fun t : ℝ ↦ (log t)⁻¹) volume a b := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
  have ht0 : 0 ≤ t := (le_min ha0 hb0).trans ht.1
  have ht1 : t < 1 := ht.2.trans_lt (max_lt ha1 hb1)
  rcases eq_or_lt_of_le ht0 with rfl | htpos
  · exact continuousAt_inv_log_zero.continuousWithinAt
  · exact ((continuousAt_log htpos.ne').inv₀ (log_neg htpos ht1).ne).continuousWithinAt

/-- The regularized integrand `(log t)⁻¹ - (t - 1)⁻¹` is interval integrable on any interval in
`[0, ∞)`. -/
theorem intervalIntegrable_inv_log_sub_inv_sub_one {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun t : ℝ ↦ (log t)⁻¹ - (t - 1)⁻¹) volume a b := by
  have hg_int : IntervalIntegrable
      (Function.update (fun t : ℝ ↦ (log t)⁻¹ - (t - 1)⁻¹) 1 (1 / 2)) volume a b :=
    (continuousOn_update_inv_log_sub_inv_sub_one.mono
      fun t (ht : t ∈ uIcc a b) ↦ (le_min ha hb).trans ht.1).intervalIntegrable
  refine hg_int.congr_ae ?_
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (1 : ℝ))] with t ht1
  exact Function.update_of_ne ht1 _ _

/-- The right-shifted regularized integrand `(log (1 + u))⁻¹ - u⁻¹` is interval integrable on
`[0, 1]`. -/
theorem intervalIntegrable_inv_log_one_add_sub_inv :
    IntervalIntegrable (fun u : ℝ ↦ (log (1 + u))⁻¹ - u⁻¹) volume 0 1 := by
  have h := intervalIntegrable_inv_log_sub_inv_sub_one (a := 1) (b := 2) zero_le_one (by norm_num)
  have h21 : (2 : ℝ) - 1 = 1 := by norm_num
  simpa [add_comm, add_sub_cancel_left, h21] using h.comp_add_left 1

/-- The left-shifted regularized integrand `(log (1 - u))⁻¹ + u⁻¹` is interval integrable on
`[0, 1]`. -/
theorem intervalIntegrable_inv_log_one_sub_add_inv :
    IntervalIntegrable (fun u : ℝ ↦ (log (1 - u))⁻¹ + u⁻¹) volume 0 1 := by
  have h := intervalIntegrable_inv_log_sub_inv_sub_one (a := 0) (b := 1) le_rfl zero_le_one
  simpa [sub_zero, sub_self, sub_sub_cancel_left, inv_neg, sub_neg_eq_add] using
    (h.comp_sub_left 1).symm

/-- The symmetric integrand `(log (1 + u))⁻¹ + (log (1 - u))⁻¹` is interval integrable on
`[0, 1]`. -/
theorem intervalIntegrable_inv_log_one_add_add_inv_log_one_sub :
    IntervalIntegrable (fun u : ℝ ↦ (log (1 + u))⁻¹ + (log (1 - u))⁻¹) volume 0 1 := by
  convert intervalIntegrable_inv_log_one_add_sub_inv.add
    intervalIntegrable_inv_log_one_sub_add_inv using 1
  ext u
  ring

end Real

namespace TauCeti.Real

/-! ### Reciprocal natural powers of the logarithm -/

/-- Reciprocal powers of the logarithm are continuous to the right of its zero `t = 1`. -/
theorem continuousOn_inv_log_pow (n : ℕ) :
    ContinuousOn (fun t : ℝ ↦ (Real.log t ^ n)⁻¹) (Ioi 1) := by
  simpa only [Real.rpow_natCast] using Real.continuousOn_inv_log_rpow (n : ℝ)

/-- The weight `t⁻¹ / log t ^ n` of integrals against powers of `1 / log` is continuous to the
right of `t = 1`. -/
theorem continuousOn_inv_div_log_pow (n : ℕ) :
    ContinuousOn (fun t : ℝ ↦ t⁻¹ / Real.log t ^ n) (Ioi 1) := by
  simpa only [div_eq_mul_inv] using
    ContinuousOn.fun_mul (continuousOn_inv₀.mono fun t (ht : t ∈ Ioi 1) ↦
      mem_compl_singleton_iff.mpr (zero_lt_one.trans ht).ne') (continuousOn_inv_log_pow n)

/-- Reciprocal powers of the logarithm are interval integrable on any interval to the right
of `1`. -/
theorem intervalIntegrable_inv_log_pow (n : ℕ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t : ℝ ↦ (Real.log t ^ n)⁻¹) volume a b := by
  simpa only [Real.rpow_natCast] using Real.intervalIntegrable_inv_log_rpow (n : ℝ) ha hb

/-- Monotonicity of the logarithm bounds `∫ t in a..b, (log t ^ n)⁻¹` above by the value of the
integrand at the left endpoint. -/
theorem integral_inv_log_pow_le (n : ℕ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, (Real.log t ^ n)⁻¹ ≤ (b - a) / Real.log a ^ n := by
  simpa only [Real.rpow_natCast] using
    Real.integral_inv_log_rpow_le (Nat.cast_nonneg n) ha hab

/-- Monotonicity of the logarithm bounds `∫ t in a..b, (log t ^ n)⁻¹` below by the value of the
integrand at the right endpoint. -/
theorem le_integral_inv_log_pow (n : ℕ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (b - a) / Real.log b ^ n ≤ ∫ t in a..b, (Real.log t ^ n)⁻¹ := by
  simpa only [Real.rpow_natCast] using
    Real.le_integral_inv_log_rpow (Nat.cast_nonneg n) ha hab

/-- The integrand `(log t ^ n)⁻¹` is nonnegative to the right of `1`, so its integral is. -/
theorem integral_inv_log_pow_nonneg (n : ℕ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    0 ≤ ∫ t in a..b, (Real.log t ^ n)⁻¹ := by
  simpa only [Real.rpow_natCast] using Real.integral_inv_log_rpow_nonneg (n : ℝ) ha hab

/-- Integration by parts for reciprocal powers of the logarithm. Both endpoints lie to the
right of `1`; the signed interval integral allows either order of the endpoints. -/
theorem integral_inv_log_pow_eq_sub_add (n : ℕ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    (∫ t in a..b, (Real.log t ^ n)⁻¹) = b / Real.log b ^ n - a / Real.log a ^ n +
      (n : ℝ) * ∫ t in a..b, (Real.log t ^ (n + 1))⁻¹ := by
  simpa only [Real.rpow_natCast, ← Nat.cast_add_one] using
    Real.integral_inv_log_rpow_eq_sub_add (n : ℝ) ha hb

end TauCeti.Real

namespace Real

open TauCeti.Real

/-- The remainder integral `∫ t in 2..x, (log t ^ n)⁻¹` is `O(x / log x ^ n)` for every
`n : ℕ`. -/
theorem isBigO_integral_inv_log_pow (n : ℕ) :
    (fun x : ℝ ↦ ∫ t in (2 : ℝ)..x, (log t ^ n)⁻¹) =O[atTop]
      fun x : ℝ ↦ x / log x ^ n := by
  have ho : (fun x : ℝ ↦ log x ^ n) =o[atTop] fun x : ℝ ↦ √x := by
    refine (isLittleO_log_rpow_rpow_atTop (r := (n : ℝ)) (s := 1 / 2)
      (by norm_num)).congr' ?_ ?_
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x _
      exact rpow_natCast _ _
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x _
      exact (sqrt_eq_rpow x).symm
  have hsqrt_le : ∀ᶠ x : ℝ in atTop, √x / log 2 ^ n ≤ x / log x ^ n := by
    have hlim : Tendsto (fun x : ℝ ↦ log x ^ n / √x) atTop (𝓝 0) :=
      ho.tendsto_div_nhds_zero
    filter_upwards [eventually_gt_atTop (2 : ℝ),
      hlim.eventually (Iio_mem_nhds (pow_pos (log_pos one_lt_two) n))]
      with x hx hratio
    have hlogx : 0 < log x := log_pos (by linarith)
    have hsqx : 0 < √x := sqrt_pos.mpr (by linarith)
    have hmul : log x ^ n ≤ log 2 ^ n * √x := (div_le_iff₀ hsqx).mp (le_of_lt hratio)
    rw [div_le_div_iff₀ (pow_pos (log_pos one_lt_two) _) (pow_pos hlogx _)]
    calc √x * log x ^ n
        ≤ √x * (log 2 ^ n * √x) := mul_le_mul_of_nonneg_left hmul hsqx.le
      _ = (√x * √x) * log 2 ^ n := by ring
      _ = x * log 2 ^ n := by rw [mul_self_sqrt (by linarith)]
  refine IsBigO.of_bound (1 + 2 ^ n) ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ), hsqrt_le] with x hx hsq
  have hlogx : 0 < log x := log_pos (by linarith)
  have hnn : 0 ≤ ∫ t in (2 : ℝ)..x, (log t ^ n)⁻¹ :=
    integral_inv_log_pow_nonneg n one_lt_two hx
  rw [norm_of_nonneg hnn, norm_of_nonneg (by positivity)]
  calc ∫ t in (2 : ℝ)..x, (log t ^ n)⁻¹
      ≤ √x / log 2 ^ n + 2 ^ n * x / log x ^ n := integral_inv_log_pow_le_sqrt_add n hx
    _ ≤ x / log x ^ n + 2 ^ n * x / log x ^ n := by gcongr
    _ = (1 + 2 ^ n) * (x / log x ^ n) := by ring

end Real

namespace TauCeti.Real

/-! ### Square-remainder and weighted reciprocal-log estimates -/

/-- `∫ t in 2..x, (log t ^ 2)⁻¹` is `o (x / log x)`, derived from
`Real.isBigO_integral_inv_log_pow 2`. -/
theorem isLittleO_integral_inv_log_sq :
    (fun x : ℝ ↦ ∫ t in (2 : ℝ)..x, (Real.log t ^ 2)⁻¹) =o[atTop] fun x : ℝ ↦ x / Real.log x := by
  have hinv : (fun x : ℝ ↦ (Real.log x)⁻¹) =o[atTop] fun _ : ℝ ↦ (1 : ℝ) :=
    (isLittleO_iff_tendsto' (Eventually.of_forall fun _ h ↦ absurd h one_ne_zero)).mpr <| by
      simpa only [Function.comp_apply, zero_div] using
        (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).div_const 1
  have hmul : (fun x : ℝ ↦ x / Real.log x ^ 2) =o[atTop] fun x : ℝ ↦ x / Real.log x := by
    simpa [div_eq_mul_inv, pow_two, mul_assoc, mul_comm, mul_left_comm] using
      hinv.mul_isBigO (isBigO_refl (fun x : ℝ ↦ x / Real.log x) atTop)
  exact (_root_.Real.isBigO_integral_inv_log_pow 2).trans_isLittleO hmul

/-- The remainder integral `∫ t in 2..x, (log t ^ 2)⁻¹` satisfies
`(∫ t in 2..x, (log t ^ 2)⁻¹) * log x / x → 0` as `x → ∞`. -/
theorem tendsto_integral_inv_log_sq_mul_log_div_atTop :
    Tendsto (fun x : ℝ ↦ (∫ t in (2 : ℝ)..x, (Real.log t ^ 2)⁻¹) * Real.log x / x)
      atTop (𝓝 0) :=
  isLittleO_integral_inv_log_sq.tendsto_div_nhds_zero.congr fun _ ↦ div_div_eq_mul_div _ _ _

/-- The weight `(t * log t ^ 2)⁻¹` is continuous to the right of `1`, so it preserves interval
integrability there. -/
theorem intervalIntegrable_div_mul_log_sq {f : ℝ → ℝ} {a b : ℝ} (ha : 1 < a) (hb : 1 < b)
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t ↦ f t / (t * Real.log t ^ 2)) volume a b := by
  simp_rw [div_eq_mul_inv]
  refine hf.mul_continuousOn fun t ht ↦ ?_
  have h1 : 1 < t := ordConnected_Ioi.uIcc_subset ha hb ht
  have h0 : t ≠ 0 := by linarith
  have hne : t * Real.log t ^ 2 ≠ 0 :=
    (mul_pos (by linarith) (pow_pos (Real.log_pos h1) 2)).ne'
  fun_prop

/-- The weight `(log t ^ 2)⁻¹` is continuous to the right of `1`, so it preserves interval
integrability there. -/
theorem intervalIntegrable_div_log_sq {g : ℝ → ℝ} {a b : ℝ} (ha : 1 < a) (hb : 1 < b)
    (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable (fun t ↦ g t / Real.log t ^ 2) volume a b := by
  simp_rw [div_eq_mul_inv]
  exact hg.mul_continuousOn ((continuousOn_inv_log_pow 2).mono (ordConnected_Ioi.uIcc_subset ha hb))

/-- Subtracting `δ t` from the integrand splits off `δ` times the remainder integral
`∫ t in a..b, (log t ^ 2)⁻¹`. -/
theorem integral_div_mul_log_sq_eq_sub_add {F : ℝ → ℝ} (δ : ℝ) {a b : ℝ} (ha : 1 < a)
    (hb : 1 < b) (hF : IntervalIntegrable F volume a b) :
    ∫ t in a..b, F t / (t * Real.log t ^ 2) =
      (∫ t in a..b, (F t - δ * t) / (t * Real.log t ^ 2)) +
        δ * ∫ t in a..b, (Real.log t ^ 2)⁻¹ := by
  have hFδ : IntervalIntegrable (fun t ↦ F t - δ * t) volume a b :=
    hF.sub ((by fun_prop : Continuous fun t : ℝ ↦ δ * t).intervalIntegrable a b)
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
    (intervalIntegrable_div_mul_log_sq ha hb hFδ)
    ((intervalIntegrable_inv_log_pow 2 ha hb).const_mul δ)]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  have ht1 : 1 < t := ordConnected_Ioi.uIcc_subset ha hb ht
  have ht0 : t ≠ 0 := by linarith
  have hlt : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
  field_simp
  ring

/-- **Comparison of weighted integrals.**  If `f t ≤ t g t` on `[a, b]` with `1 < a ≤ b`, then
`∫ t in a..b, f t / (t log² t) ≤ ∫ t in a..b, g t / log² t`. -/
theorem integral_div_mul_log_sq_le_integral_div_log_sq {f g : ℝ → ℝ} {a b : ℝ} (ha : 1 < a)
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
    (h : ∀ t ∈ Icc a b, f t ≤ t * g t) :
    ∫ t in a..b, f t / (t * Real.log t ^ 2) ≤ ∫ t in a..b, g t / Real.log t ^ 2 := by
  have hb : 1 < b := ha.trans_le hab
  refine intervalIntegral.integral_mono_on hab (intervalIntegrable_div_mul_log_sq ha hb hf)
    (intervalIntegrable_div_log_sq ha hb hg) fun t ht ↦ ?_
  have ht1 : 1 < t := ha.trans_le ht.1
  have ht0 : 0 < t := zero_lt_one.trans ht1
  have hL : 0 < Real.log t ^ 2 := pow_pos (Real.log_pos ht1) 2
  calc f t / (t * Real.log t ^ 2) ≤ t * g t / (t * Real.log t ^ 2) :=
        div_le_div_of_nonneg_right (h t ht) (mul_pos ht0 hL).le
    _ = g t / Real.log t ^ 2 := mul_div_mul_left _ _ ht0.ne'

/-- **Lower comparison of weighted integrals.**  If `-(t g t) ≤ f t` on `[a, b]` with
`1 < a ≤ b`, then `-∫ t in a..b, g t / log² t ≤ ∫ t in a..b, f t / (t log² t)`. -/
theorem neg_integral_div_log_sq_le_integral_div_mul_log_sq {f g : ℝ → ℝ} {a b : ℝ} (ha : 1 < a)
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
    (h : ∀ t ∈ Icc a b, -(t * g t) ≤ f t) :
    -∫ t in a..b, g t / Real.log t ^ 2 ≤ ∫ t in a..b, f t / (t * Real.log t ^ 2) := by
  have hneg := integral_div_mul_log_sq_le_integral_div_log_sq ha hab hf.neg hg
    fun t ht ↦ neg_le.mp (h t ht)
  simp only [Pi.neg_apply, neg_div, intervalIntegral.integral_neg] at hneg
  exact neg_le.mp hneg

/-- **Two-sided comparison of weighted integrals.**  If `|f t| ≤ t g t` on `[a, b]` with
`1 < a ≤ b`, then `|∫ t in a..b, f t / (t log² t)| ≤ ∫ t in a..b, g t / log² t`. -/
theorem abs_integral_div_mul_log_sq_le_integral_div_log_sq {f g : ℝ → ℝ} {a b : ℝ} (ha : 1 < a)
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
    (h : ∀ t ∈ Icc a b, |f t| ≤ t * g t) :
    |∫ t in a..b, f t / (t * Real.log t ^ 2)| ≤ ∫ t in a..b, g t / Real.log t ^ 2 :=
  abs_le.mpr ⟨neg_integral_div_log_sq_le_integral_div_mul_log_sq ha hab hf hg
    fun t ht ↦ (abs_le.mp (h t ht)).1, integral_div_mul_log_sq_le_integral_div_log_sq ha hab hf hg
    fun t ht ↦ (le_abs_self (f t)).trans (h t ht)⟩

/-- Splitting at a cutoff `T` beyond which `|f t| ≤ c t`, the weighted integral of `f` on `a..x`
is bounded by its own initial segment `a..T` plus `c` times `∫ t in a..x, (log t ^ 2)⁻¹`. -/
theorem abs_integral_div_mul_log_sq_le_add {f : ℝ → ℝ} {a T x c : ℝ} (ha : 1 < a)
    (haT : a ≤ T) (hTx : T ≤ x) (hf : IntervalIntegrable f volume a x)
    (h : ∀ t ∈ Icc T x, |f t| ≤ c * t) :
    |∫ t in a..x, f t / (t * Real.log t ^ 2)| ≤
      |∫ t in a..T, f t / (t * Real.log t ^ 2)| + c * ∫ t in a..x, (Real.log t ^ 2)⁻¹ := by
  have hT1 : 1 < T := ha.trans_le haT
  have hx1 : 1 < x := hT1.trans_le hTx
  have hax : a ≤ x := haT.trans hTx
  have hc0 : 0 ≤ c := by nlinarith [h T ⟨le_rfl, hTx⟩, abs_nonneg (f T)]
  have hf_head : IntervalIntegrable f volume a T := hf.mono_set <| by
    rw [uIcc_of_le haT, uIcc_of_le hax]; exact Icc_subset_Icc le_rfl hTx
  have hf_tail : IntervalIntegrable f volume T x := hf.mono_set <| by
    rw [uIcc_of_le hTx, uIcc_of_le hax]; exact Icc_subset_Icc haT le_rfl
  have htail : |∫ t in T..x, f t / (t * Real.log t ^ 2)| ≤
      c * ∫ t in T..x, (Real.log t ^ 2)⁻¹ := by
    simpa only [div_eq_mul_inv, intervalIntegral.integral_const_mul] using
      abs_integral_div_mul_log_sq_le_integral_div_log_sq (g := fun _ ↦ c) hT1 hTx hf_tail
        intervalIntegrable_const fun t ht ↦ (h t ht).trans_eq (mul_comm c t)
  have hJ : (∫ t in T..x, (Real.log t ^ 2)⁻¹) ≤ ∫ t in a..x, (Real.log t ^ 2)⁻¹ := by
    linarith [integral_inv_log_pow_nonneg 2 ha haT,
      intervalIntegral.integral_add_adjacent_intervals
        (a := a) (b := T) (c := x) (f := fun t : ℝ ↦ (Real.log t ^ 2)⁻¹)
        (intervalIntegrable_inv_log_pow 2 ha hT1)
        (intervalIntegrable_inv_log_pow 2 hT1 hx1)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_div_mul_log_sq ha hT1 hf_head)
    (intervalIntegrable_div_mul_log_sq hT1 hx1 hf_tail)]
  calc |(∫ t in a..T, f t / (t * Real.log t ^ 2)) +
          ∫ t in T..x, f t / (t * Real.log t ^ 2)|
      ≤ |∫ t in a..T, f t / (t * Real.log t ^ 2)| +
          |∫ t in T..x, f t / (t * Real.log t ^ 2)| := abs_add_le _ _
    _ ≤ _ := by gcongr; exact htail.trans (mul_le_mul_of_nonneg_left hJ hc0)

/-- **A linearly bounded integrand leaves a negligible remainder.**  If `f` is interval integrable
above `2` and satisfies `f = O(x)`, then `∫ t in 2..x, f t / (t * log t ^ 2)` is `o (x / log x)`.

For the rational Chebyshev function this is `Chebyshev.integral_theta_div_log_sq_isLittleO`. -/
theorem isLittleO_integral_div_mul_log_sq {f : ℝ → ℝ}
    (hf_int : ∀ x, 2 ≤ x → IntervalIntegrable f volume 2 x) (hf : f =O[atTop] id) :
    (fun x : ℝ ↦ ∫ t in (2 : ℝ)..x, f t / (t * Real.log t ^ 2)) =o[atTop]
      fun x : ℝ ↦ x / Real.log x := by
  -- Choose a cutoff `T ≥ 2` beyond which `|f t| ≤ c * t`.
  obtain ⟨c, hc⟩ := hf.bound
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hc.and (eventually_ge_atTop (2 : ℝ)))
  have hT2 : (2 : ℝ) ≤ T := (hT T le_rfl).2
  have hbound : ∀ t, T ≤ t → |f t| ≤ c * t := fun t ht ↦ by
    simpa [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t)] using (hT t ht).1
  have hc0 : 0 ≤ c := by nlinarith [hbound T le_rfl, abs_nonneg (f T)]
  -- Both summands of `abs_integral_div_mul_log_sq_le_add` are `o (x / log x)`.
  have hconst := _root_.Real.isLittleO_const_div_log |∫ t in (2 : ℝ)..T, f t / (t * Real.log t ^ 2)|
  have hrem : (fun x : ℝ ↦ c * ∫ t in (2 : ℝ)..x, (Real.log t ^ 2)⁻¹) =o[atTop]
      fun x : ℝ ↦ x / Real.log x := isLittleO_integral_inv_log_sq.const_mul_left c
  rw [isLittleO_iff]
  intro ε hε
  filter_upwards [eventually_ge_atTop T, hconst.bound (half_pos hε), hrem.bound (half_pos hε)]
    with x hx h1 h2
  rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)] at h1
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg hc0 (integral_inv_log_pow_nonneg 2 one_lt_two (hT2.trans hx)))] at h2
  calc ‖∫ t in (2 : ℝ)..x, f t / (t * Real.log t ^ 2)‖
      = |∫ t in (2 : ℝ)..x, f t / (t * Real.log t ^ 2)| := Real.norm_eq_abs _
    _ ≤ _ := abs_integral_div_mul_log_sq_le_add one_lt_two hT2 hx (hf_int x (hT2.trans hx))
        fun t ht ↦ hbound t ht.1
    _ ≤ ε / 2 * ‖x / Real.log x‖ + ε / 2 * ‖x / Real.log x‖ := add_le_add h1 h2
    _ = ε * ‖x / Real.log x‖ := by ring

end TauCeti.Real
