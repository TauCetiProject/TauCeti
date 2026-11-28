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
import TauCeti.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Analysis.SpecialFunctions.Log.InvLog

/-!
# Integrals of reciprocal logarithms and their powers

This file establishes continuity, interval integrability, monotonicity bounds, integration by parts,
and explicit remainder estimates for reciprocal powers `(log t ^ k)⁻¹` and `(log t ^ n)⁻¹`, as well
as interval integrability of `(log t)⁻¹` on `[0, 1)`, the pole-subtracted integrand
`(log t)⁻¹ - (t - 1)⁻¹` on `[0, ∞)`, and the symmetrically folded integrand
`(log (1 + u))⁻¹ + (log (1 - u))⁻¹` on `[0, 1]`.

Separating these integrand and integral lemmas from
`TauCeti.Analysis.SpecialFunctions.LogIntegral.Basic` lets consumers of reciprocal-log integrals
import them directly without depending on `TauCeti.Real.logIntegral`, `TauCeti.Real.li`, or
`Real.eulerMascheroniConstant`.

## Main declarations

* `TauCeti.Real.continuousOn_inv_log_rpow`, `TauCeti.Real.intervalIntegrable_inv_log_rpow`,
  `TauCeti.Real.integral_inv_log_rpow_le`, `TauCeti.Real.le_integral_inv_log_rpow`,
  `TauCeti.Real.integral_inv_log_rpow_nonneg`, `TauCeti.Real.integral_inv_log_rpow_eq_sub_add` —
  continuity, monotonicity bounds (for `0 ≤ k` and `1 < a ≤ b`), nonnegativity (for
  `1 < a ≤ b`), and integration by parts for reciprocal real powers `(log t ^ k)⁻¹` with
  `a, b > 1`.
* `TauCeti.Real.integral_inv_log_rpow_le_sqrt_add`,
  `TauCeti.Real.integral_inv_log_rpow_lt_div_add`,
  `TauCeti.Real.integral_inv_log_pow_le_sqrt_add`,
  `TauCeti.Real.integral_inv_log_pow_lt_div_add`,
  `TauCeti.Real.isBigO_integral_inv_log_pow` — explicit upper bounds for
  `∫ t in 2..x, (log t ^ k)⁻¹` and the `O(x / log x ^ n)` remainder estimate for natural
  exponents `n : ℕ`.
* `TauCeti.Real.continuousOn_inv_log_pow`, `TauCeti.Real.intervalIntegrable_inv_log_pow`,
  `TauCeti.Real.integral_inv_log_pow_le`, `TauCeti.Real.le_integral_inv_log_pow`,
  `TauCeti.Real.integral_inv_log_pow_nonneg`, `TauCeti.Real.integral_inv_log_pow_eq_sub_add` —
  natural-exponent specializations.
* `TauCeti.Real.intervalIntegrable_inv_log_of_lt_one` — interval integrability of `(log t)⁻¹` on
  `[0, 1)`.
* `TauCeti.Real.intervalIntegrable_inv_log_sub_inv_sub_one`,
  `TauCeti.Real.intervalIntegrable_inv_log_one_add_sub_inv`,
  `TauCeti.Real.intervalIntegrable_inv_log_one_sub_add_inv`,
  `TauCeti.Real.intervalIntegrable_inv_log_one_add_add_inv_log_one_sub` — interval integrability
  of the pole-subtracted and symmetrically folded integrands.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapters 7 and 18.
* The integration-by-parts recurrence is adapted from the Ramanujan estimates in the
  [PrimeNumberTheoremAnd project](https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/dc6e36e/PrimeNumberTheoremAnd/IEANTN/Ramanujan/Ramanujan.lean).
-/

public section

open Asymptotics Filter MeasureTheory Real Set
open scoped Topology

namespace TauCeti.Real

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
  have h := (intervalIntegrable_inv_log_sub_inv_sub_one (a := 1) (b := 2)
    zero_le_one (by norm_num)).comp_add_left 1
  have hfun : (fun u : ℝ ↦ (log (1 + u))⁻¹ - (1 + u - 1)⁻¹) =
      fun u : ℝ ↦ (log (1 + u))⁻¹ - u⁻¹ := by
    ext u
    ring
  have h21 : (2 : ℝ) - 1 = 1 := by norm_num
  rw [hfun, sub_self, h21] at h
  exact h

/-- The left-shifted regularized integrand `(log (1 - u))⁻¹ + u⁻¹` is interval integrable on
`[0, 1]`. -/
theorem intervalIntegrable_inv_log_one_sub_add_inv :
    IntervalIntegrable (fun u : ℝ ↦ (log (1 - u))⁻¹ + u⁻¹) volume 0 1 := by
  have h := ((intervalIntegrable_inv_log_sub_inv_sub_one (a := 0) (b := 1)
    le_rfl zero_le_one).comp_sub_left 1).symm
  have hfun : (fun u : ℝ ↦ (log (1 - u))⁻¹ - (1 - u - 1)⁻¹) =
      fun u : ℝ ↦ (log (1 - u))⁻¹ + u⁻¹ := by
    ext u
    ring
  rw [hfun, sub_self, sub_zero] at h
  exact h

/-- The symmetric integrand `(log (1 + u))⁻¹ + (log (1 - u))⁻¹` is interval integrable on
`[0, 1]`. -/
theorem intervalIntegrable_inv_log_one_add_add_inv_log_one_sub :
    IntervalIntegrable (fun u : ℝ ↦ (log (1 + u))⁻¹ + (log (1 - u))⁻¹) volume 0 1 := by
  convert intervalIntegrable_inv_log_one_add_sub_inv.add
    intervalIntegrable_inv_log_one_sub_add_inv using 1
  ext u
  ring

/-! ### Reciprocal natural powers of the logarithm -/

/-- Reciprocal powers of the logarithm are continuous to the right of its zero `t = 1`. -/
theorem continuousOn_inv_log_pow (n : ℕ) :
    ContinuousOn (fun t : ℝ ↦ (Real.log t ^ n)⁻¹) (Ioi 1) := by
  simpa only [Real.rpow_natCast] using continuousOn_inv_log_rpow (n : ℝ)

/-- Reciprocal powers of the logarithm are interval integrable on any interval to the right
of `1`. -/
theorem intervalIntegrable_inv_log_pow (n : ℕ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t : ℝ ↦ (Real.log t ^ n)⁻¹) volume a b := by
  simpa only [Real.rpow_natCast] using intervalIntegrable_inv_log_rpow (n : ℝ) ha hb

/-- Monotonicity of the logarithm bounds `∫ t in a..b, (log t ^ n)⁻¹` above by the value of the
integrand at the left endpoint. -/
theorem integral_inv_log_pow_le (n : ℕ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, (Real.log t ^ n)⁻¹ ≤ (b - a) / Real.log a ^ n := by
  simpa only [Real.rpow_natCast] using
    integral_inv_log_rpow_le (Nat.cast_nonneg n) ha hab

/-- Monotonicity of the logarithm bounds `∫ t in a..b, (log t ^ n)⁻¹` below by the value of the
integrand at the right endpoint. -/
theorem le_integral_inv_log_pow (n : ℕ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (b - a) / Real.log b ^ n ≤ ∫ t in a..b, (Real.log t ^ n)⁻¹ := by
  simpa only [Real.rpow_natCast] using
    le_integral_inv_log_rpow (Nat.cast_nonneg n) ha hab

/-- The integrand `(log t ^ n)⁻¹` is nonnegative to the right of `1`, so its integral is. -/
theorem integral_inv_log_pow_nonneg (n : ℕ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    0 ≤ ∫ t in a..b, (Real.log t ^ n)⁻¹ := by
  simpa only [Real.rpow_natCast] using integral_inv_log_rpow_nonneg (n : ℝ) ha hab

/-- Integration by parts for reciprocal powers of the logarithm. Both endpoints lie to the
right of `1`; the signed interval integral allows either order of the endpoints. -/
theorem integral_inv_log_pow_eq_sub_add (n : ℕ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    (∫ t in a..b, (Real.log t ^ n)⁻¹) = b / Real.log b ^ n - a / Real.log a ^ n +
      (n : ℝ) * ∫ t in a..b, (Real.log t ^ (n + 1))⁻¹ := by
  simpa only [Real.rpow_natCast, ← Nat.cast_add_one] using
    integral_inv_log_rpow_eq_sub_add (n : ℝ) ha hb

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

end TauCeti.Real
