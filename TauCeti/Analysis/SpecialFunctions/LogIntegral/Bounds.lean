/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.LogIntegral.Unoffset
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Explicit bounds, asymptotic expansion, and numerical enclosures for `li` and `Li`

This file develops explicit bounds and asymptotics for the offset and unoffset logarithmic
integrals `TauCeti.Real.logIntegral` (`Li`) and `TauCeti.Real.li` (`li`).

## Main results

### Explicit integrals of reciprocal real powers of `log`
* `TauCeti.Real.integral_inv_log_rpow_eq_sub_add`: integration by parts for
  `∫ t in a..b, (log t ^ k)⁻¹` with any real exponent `k`.
* `TauCeti.Real.integral_inv_log_rpow_le_sqrt_add` and
  `TauCeti.Real.integral_inv_log_rpow_lt_div_add`: splitting at `√x` bounds
  `∫ t in a..x, (log t ^ k)⁻¹` by `√x / log a ^ k + 2 ^ k * x / log x ^ k` and hence by
  `x / log x ^ k + k * (√x / log a ^ (k + 1) + 2 ^ (k + 1) * x / log x ^ (k + 1))`
  for all `0 ≤ k` and `1 < a ≤ x`, together with natural-exponent specializations.

### Asymptotic expansion of `Li` and `li`
* `TauCeti.Real.integral_inv_log_eq_sum_factorial_div_log_add`: `n`-fold integration by parts of
  `∫ t in a..x, (log t)⁻¹` with explicit remainder `n! ∫ t in a..x, (log t ^ (n + 1))⁻¹`.
* `TauCeti.Real.logIntegral_sub_sum_factorial_div_log_isBigO` and
  `TauCeti.Real.li_sub_sum_factorial_div_log_isBigO`: for every `n : ℕ`,
  `Li x = (x / log x) ∑_{k < n} k! / log x ^ k + O(x / log x ^ (n + 1))` and the same for `li x`.
* `TauCeti.Real.li_isEquivalent_logIntegral` and `TauCeti.Real.li_isEquivalent_div_log`:
  `li x ~ Li x ~ x / log x` as `x → ∞`.

### Series truncation bounds and numerical enclosures of `li 2`
* `TauCeti.Real.sum_range_le_tsum_pow_div_mul_factorial` and
  `TauCeti.Real.tsum_pow_div_mul_factorial_le_sum_range_add`: lower partial-sum bound and upper
  geometric-tail bound for `∑' n, y ^ (n + 1) / ((n + 1) * (n + 1)!)`.
* `TauCeti.Real.le_li_two_sub_eulerMascheroniConstant` and
  `TauCeti.Real.li_two_sub_eulerMascheroniConstant_le`: `0.467948 ≤ li 2 - γ ≤ 0.467950`, yielding
  the unconditional enclosure `0.96 < li 2 < 1.14` and, under `|γ - 0.5772156649| < 10⁻⁹`, the
  tight enclosure `1.0451 ≤ li 2 ≤ 1.0452`.

### The difference `Li x - x / log x`
* `TauCeti.Real.strictMonoOn_logIntegral_sub_div_log`: `x ↦ Li x - x / log x` is strictly
  increasing on `(1, ∞)` with derivative `(log x ^ 2)⁻¹`.
* `TauCeti.Real.le_logIntegral_sub_div_log`, `TauCeti.Real.lt_logIntegral_sub_div_log`, and
  `TauCeti.Real.logIntegral_sub_div_log_lt`: explicit two-sided bounds for `x ≥ 2`.
* `TauCeti.Real.existsUnique_logIntegral_sub_div_log_eq_zero` and
  `TauCeti.Real.logIntegral_sub_div_log_eq_zero_mem_Ioo`: `Li x - x / log x` has a unique zero
  in `(1, ∞)`, located in `(6.5797, 6.5798)`.
* `TauCeti.Real.sub_div_log_sq_lt_logIntegral_sub_div_log`: for `6.5798 ≤ a ≤ x`,
  `(x - a) / log x ^ 2 < Li x - x / log x`, in particular
  `(x - 6.58) / log x ^ 2 ≤ Li x - x / log x` for `6.58 ≤ x` (Fiori–Kadiri–Swidinsky, Lemma 20).

## References

* A. Fiori, H. Kadiri, J. Swidinsky, *Sharper bounds for the Chebyshev function ψ(x)*,
  Journal of Mathematical Analysis and Applications 527 (2023), Lemma 20.
-/

public section

namespace TauCeti.Real

open Asymptotics Filter MeasureTheory Set
open scoped Topology

/-! ### Explicit integrals of reciprocal real powers of the logarithm -/

/-- Reciprocal real powers of the logarithm are continuous on `(1, ∞)`. -/
theorem continuousOn_inv_log_rpow (k : ℝ) :
    ContinuousOn (fun t : ℝ ↦ (Real.log t ^ k)⁻¹) (Ioi 1) := by
  have hlog : ContinuousOn (fun t : ℝ ↦ Real.log t) (Ioi 1) :=
    Real.continuousOn_log.mono fun t ht ↦ ne_of_gt (lt_trans one_pos ht)
  exact (hlog.rpow_const fun t ht ↦ Or.inl (Real.log_pos ht).ne').inv₀
    fun t ht ↦ (Real.rpow_pos_of_pos (Real.log_pos ht) k).ne'

/-- Reciprocal real powers of the logarithm are interval integrable on any interval in `(1, ∞)`. -/
theorem intervalIntegrable_inv_log_rpow (k : ℝ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t : ℝ ↦ (Real.log t ^ k)⁻¹) volume a b := by
  refine ((continuousOn_inv_log_rpow k).mono fun t ht ↦ ?_).intervalIntegrable
  rcases mem_uIcc.mp ht with h | h
  · exact ha.trans_le h.1
  · exact hb.trans_le h.1

/-- Integration by parts for reciprocal real powers of the logarithm on `(1, ∞)`, with either
orientation of the interval. -/
theorem integral_inv_log_rpow_eq_sub_add (k : ℝ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    (∫ t in a..b, (Real.log t ^ k)⁻¹) = b / Real.log b ^ k - a / Real.log a ^ k +
      k * ∫ t in a..b, (Real.log t ^ (k + 1))⁻¹ := by
  have hi := intervalIntegrable_inv_log_rpow k ha hb
  have hi1 := intervalIntegrable_inv_log_rpow (k + 1) ha hb
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hasDerivAt_div_log_rpow k (Real.log_pos (by
      rcases mem_uIcc.mp ht with h | h
      · exact ha.trans_le h.1
      · exact hb.trans_le h.1))) (hi.sub (hi1.const_mul k))
  rw [intervalIntegral.integral_sub hi (hi1.const_mul k),
    intervalIntegral.integral_const_mul] at hFTC
  exact sub_eq_iff_eq_add.mp hFTC

/-- Monotonicity of the logarithm bounds `∫ t in a..b, (log t ^ k)⁻¹` above by the integrand at
the left endpoint, for every real `k ≥ 0`. -/
theorem integral_inv_log_rpow_le {k a b : ℝ} (hk : 0 ≤ k) (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, (Real.log t ^ k)⁻¹ ≤ (b - a) / Real.log a ^ k := by
  have hla : 0 < Real.log a := Real.log_pos ha
  have hb : 1 < b := ha.trans_le hab
  have hmono := intervalIntegral.integral_mono_on hab (intervalIntegrable_inv_log_rpow k ha hb)
    (g := fun _ ↦ (Real.log a ^ k)⁻¹) intervalIntegrable_const fun t ht ↦ ?_
  · simpa [smul_eq_mul, div_eq_mul_inv] using hmono
  · exact inv_anti₀ (Real.rpow_pos_of_pos hla k)
      (Real.rpow_le_rpow hla.le (Real.log_le_log (by linarith) ht.1) hk)

/-- Monotonicity of the logarithm bounds `∫ t in a..b, (log t ^ k)⁻¹` below by the integrand at
the right endpoint, for every real `k ≥ 0`. -/
theorem le_integral_inv_log_rpow {k a b : ℝ} (hk : 0 ≤ k) (ha : 1 < a) (hab : a ≤ b) :
    (b - a) / Real.log b ^ k ≤ ∫ t in a..b, (Real.log t ^ k)⁻¹ := by
  have hla : 0 < Real.log a := Real.log_pos ha
  have hb : 1 < b := ha.trans_le hab
  have hmono := intervalIntegral.integral_mono_on hab
    (f := fun _ ↦ (Real.log b ^ k)⁻¹) intervalIntegrable_const
    (intervalIntegrable_inv_log_rpow k ha hb) fun t ht ↦ ?_
  · simpa [smul_eq_mul, div_eq_mul_inv] using hmono
  · have hlt : 0 < Real.log t := hla.trans_le (Real.log_le_log (by linarith) ht.1)
    exact inv_anti₀ (Real.rpow_pos_of_pos hlt k)
      (Real.rpow_le_rpow hlt.le (Real.log_le_log (by linarith [ht.1]) ht.2) hk)

/-- The integrand `(log t ^ k)⁻¹` is nonnegative on `(1, ∞)`, so its integral is nonnegative. -/
theorem integral_inv_log_rpow_nonneg (k : ℝ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    0 ≤ ∫ t in a..b, (Real.log t ^ k)⁻¹ := by
  refine intervalIntegral.integral_nonneg hab fun t ht ↦ ?_
  exact inv_nonneg.mpr (Real.rpow_nonneg (Real.log_pos (ha.trans_le ht.1)).le k)

/-- Splitting at `√x` (when `a ^ 2 ≤ x`) or using `log a > log x / 2` (when `x < a ^ 2`) bounds
`∫ t in a..x, (log t ^ k)⁻¹` by `√x / log a ^ k + 2 ^ k * x / log x ^ k` for all `0 ≤ k` and
`1 < a ≤ x`. -/
theorem integral_inv_log_rpow_le_sqrt_add {k a x : ℝ} (hk : 0 ≤ k) (ha : 1 < a) (hax : a ≤ x) :
    ∫ t in a..x, (Real.log t ^ k)⁻¹ ≤ √x / Real.log a ^ k + (2 : ℝ) ^ k * x / Real.log x ^ k := by
  have hx1 : 1 < x := ha.trans_le hax
  have hx0 : 0 < x := by linarith
  have hla : 0 < Real.log a := Real.log_pos ha
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hdiv : (Real.log x / 2) ^ k = Real.log x ^ k / (2 : ℝ) ^ k :=
    Real.div_rpow hlx.le (by norm_num) k
  by_cases hsq : a ^ 2 ≤ x
  · -- Case 1: `a ^ 2 ≤ x`; split the integral at `√x ∈ [a, x]`.
    have ha_sq : a ≤ √x := by
      have := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (by linarith : (0 : ℝ) ≤ a)] at this
    have hsq_x : √x ≤ x := by
      rw [Real.sqrt_le_self_iff]
      exact Or.inr hx1.le
    have hsq1 : 1 < √x := ha.trans_le ha_sq
    have hsplit : (∫ t in a..x, (Real.log t ^ k)⁻¹) =
        (∫ t in a..√x, (Real.log t ^ k)⁻¹) + ∫ t in √x..x, (Real.log t ^ k)⁻¹ :=
      (intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_inv_log_rpow k ha hsq1)
        (intervalIntegrable_inv_log_rpow k hsq1 hx1)).symm
    have hb₁ : (∫ t in a..√x, (Real.log t ^ k)⁻¹) ≤ √x / Real.log a ^ k := by
      refine (integral_inv_log_rpow_le hk ha ha_sq).trans ?_
      exact div_le_div_of_nonneg_right (by linarith) (Real.rpow_pos_of_pos hla k).le
    have hb₂ : (∫ t in √x..x, (Real.log t ^ k)⁻¹) ≤ (2 : ℝ) ^ k * x / Real.log x ^ k := by
      refine (integral_inv_log_rpow_le hk hsq1 hsq_x).trans ?_
      rw [Real.log_sqrt hx0.le, hdiv, div_div_eq_mul_div, mul_comm (x - √x)]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith [Real.sqrt_nonneg x]) (by positivity))
        (Real.rpow_pos_of_pos hlx k).le
    rw [hsplit]
    exact add_le_add hb₁ hb₂
  · -- Case 2: `x < a ^ 2`; every `t ∈ [a, x]` already satisfies `log t ≥ log a > log x / 2`.
    push Not at hsq
    have hhalf : Real.log x / 2 ≤ Real.log a := by
      have hlog : Real.log x < Real.log (a ^ 2) := Real.log_lt_log hx0 hsq
      rw [Real.log_pow] at hlog
      norm_num at hlog
      linarith
    have hpow_le : (Real.log x / 2) ^ k ≤ Real.log a ^ k :=
      Real.rpow_le_rpow (by positivity) hhalf hk
    have hb : (∫ t in a..x, (Real.log t ^ k)⁻¹) ≤ (2 : ℝ) ^ k * x / Real.log x ^ k := by
      calc (∫ t in a..x, (Real.log t ^ k)⁻¹)
          ≤ (x - a) / Real.log a ^ k := integral_inv_log_rpow_le hk ha hax
        _ ≤ x / Real.log a ^ k :=
            div_le_div_of_nonneg_right (by linarith) (Real.rpow_pos_of_pos hla k).le
        _ ≤ x / (Real.log x / 2) ^ k :=
            div_le_div_of_nonneg_left hx0.le (Real.rpow_pos_of_pos (by positivity) k) hpow_le
        _ = (2 : ℝ) ^ k * x / Real.log x ^ k := by
            rw [hdiv, div_div_eq_mul_div, mul_comm]
    have hnn : 0 ≤ √x / Real.log a ^ k :=
      div_nonneg (Real.sqrt_nonneg x) (Real.rpow_pos_of_pos hla k).le
    linarith

/-- One integration by parts followed by `integral_inv_log_rpow_le_sqrt_add` yields an explicit
strict upper bound for `∫ t in a..x, (log t ^ k)⁻¹` for all `0 ≤ k` and `1 < a ≤ x`. -/
theorem integral_inv_log_rpow_lt_div_add {k a x : ℝ} (hk : 0 ≤ k) (ha : 1 < a) (hax : a ≤ x) :
    ∫ t in a..x, (Real.log t ^ k)⁻¹ <
      x / Real.log x ^ k +
        k * (√x / Real.log a ^ (k + 1) + (2 : ℝ) ^ (k + 1) * x / Real.log x ^ (k + 1)) := by
  have hx1 : 1 < x := ha.trans_le hax
  rw [integral_inv_log_rpow_eq_sub_add k ha hx1]
  have hrem := integral_inv_log_rpow_le_sqrt_add (by linarith : 0 ≤ k + 1) ha hax
  have hpos : 0 < a / Real.log a ^ k :=
    div_pos (by linarith) (Real.rpow_pos_of_pos (Real.log_pos ha) k)
  have hmul := mul_le_mul_of_nonneg_left hrem hk
  linarith

/-- Natural-exponent specialization of `integral_inv_log_rpow_le_sqrt_add`. -/
theorem integral_inv_log_pow_le_sqrt_add (n : ℕ) {a x : ℝ} (ha : 1 < a) (hax : a ≤ x) :
    ∫ t in a..x, (Real.log t ^ n)⁻¹ ≤ √x / Real.log a ^ n + (2 : ℝ) ^ n * x / Real.log x ^ n := by
  simpa only [Real.rpow_natCast] using
    integral_inv_log_rpow_le_sqrt_add (Nat.cast_nonneg n) ha hax

/-- Natural-exponent specialization of `integral_inv_log_rpow_lt_div_add`. -/
theorem integral_inv_log_pow_lt_div_add (n : ℕ) {a x : ℝ} (ha : 1 < a) (hax : a ≤ x) :
    ∫ t in a..x, (Real.log t ^ n)⁻¹ <
      x / Real.log x ^ n +
        (n : ℝ) * (√x / Real.log a ^ (n + 1) + (2 : ℝ) ^ (n + 1) * x / Real.log x ^ (n + 1)) := by
  have h := integral_inv_log_rpow_lt_div_add (Nat.cast_nonneg n) ha hax
  simpa only [← Nat.cast_add_one, Real.rpow_natCast] using h

/-! ### Asymptotic expansion of `logIntegral` and `li` -/

/-- For every real `k`, `x / log x ^ k → ∞` as `x → ∞`. -/
theorem tendsto_div_log_rpow_atTop (k : ℝ) :
    Tendsto (fun x : ℝ ↦ x / Real.log x ^ k) atTop atTop := by
  have hzero : Tendsto (fun x : ℝ ↦ Real.log x ^ k / x) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      (_root_.isLittleO_log_rpow_rpow_atTop k zero_lt_one).tendsto_div_nhds_zero
  have hgt : Tendsto (fun x : ℝ ↦ Real.log x ^ k / x) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hzero ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (Real.rpow_pos_of_pos (Real.log_pos hx) k) (by linarith)
  exact hgt.inv_tendsto_nhdsGT_zero.congr fun x ↦ inv_div _ _

/-- Every constant is `o(x / log x ^ k)` as `x → ∞`, for any real exponent `k`. -/
theorem isLittleO_const_div_log_rpow (c k : ℝ) :
    (fun _ : ℝ ↦ c) =o[atTop] fun x : ℝ ↦ x / Real.log x ^ k :=
  isLittleO_const_left.mpr <| Or.inr <|
    (tendsto_abs_atTop_atTop.comp (tendsto_div_log_rpow_atTop k)).congr
      fun _ ↦ (Real.norm_eq_abs _).symm

/-- For every real `k ≥ 0` and `1 < a`, `∫ t in a..x, (log t ^ k)⁻¹ = O(x / log x ^ k)`
as `x → ∞`. -/
theorem integral_inv_log_rpow_isBigO {k a : ℝ} (hk : 0 ≤ k) (ha : 1 < a) :
    (fun x : ℝ ↦ ∫ t in a..x, (Real.log t ^ k)⁻¹) =O[atTop] fun x : ℝ ↦ x / Real.log x ^ k := by
  have hlim : Tendsto (fun x : ℝ ↦ Real.log x ^ k / √x) atTop (𝓝 0) := by
    refine ((_root_.isLittleO_log_rpow_rpow_atTop k
      (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x _
    rw [Real.sqrt_eq_rpow]
  have hla : 0 < Real.log a ^ k := Real.rpow_pos_of_pos (Real.log_pos ha) k
  refine IsBigO.of_bound ((2 : ℝ) ^ k + 1) ?_
  filter_upwards [eventually_ge_atTop a,
    hlim.eventually (gt_mem_nhds hla)] with x hax hlt
  have hx1 : 1 < x := ha.trans_le hax
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x ^ k := Real.rpow_pos_of_pos (Real.log_pos hx1) k
  have hsq_pos : 0 < √x := Real.sqrt_pos.mpr hx0
  have hnn := integral_inv_log_rpow_nonneg k ha hax
  have hsqrt_le : √x / Real.log a ^ k ≤ x / Real.log x ^ k := by
    rw [div_le_div_iff₀ hla hlx]
    have h1 : Real.log x ^ k ≤ Real.log a ^ k * √x := (div_le_iff₀ hsq_pos).mp hlt.le
    calc √x * Real.log x ^ k
        ≤ √x * (Real.log a ^ k * √x) := mul_le_mul_of_nonneg_left h1 hsq_pos.le
      _ = x * Real.log a ^ k := by
          rw [mul_left_comm, Real.mul_self_sqrt hx0.le, mul_comm]
  rw [Real.norm_of_nonneg hnn, Real.norm_of_nonneg (div_nonneg hx0.le hlx.le)]
  calc (∫ t in a..x, (Real.log t ^ k)⁻¹)
      ≤ √x / Real.log a ^ k + (2 : ℝ) ^ k * x / Real.log x ^ k :=
        integral_inv_log_rpow_le_sqrt_add hk ha hax
    _ ≤ x / Real.log x ^ k + (2 : ℝ) ^ k * x / Real.log x ^ k :=
        add_le_add hsqrt_le le_rfl
    _ = ((2 : ℝ) ^ k + 1) * (x / Real.log x ^ k) := by ring

/-- Natural-exponent specialization of `integral_inv_log_rpow_isBigO`. -/
theorem integral_inv_log_pow_isBigO (n : ℕ) {a : ℝ} (ha : 1 < a) :
    (fun x : ℝ ↦ ∫ t in a..x, (Real.log t ^ n)⁻¹) =O[atTop] fun x : ℝ ↦ x / Real.log x ^ n := by
  simpa only [Real.rpow_natCast] using integral_inv_log_rpow_isBigO (Nat.cast_nonneg n) ha

/-- `n`-fold integration by parts for `∫ t in a..x, (log t)⁻¹`, valid for any `1 < a` and
`1 < x` with either orientation. -/
theorem integral_inv_log_eq_sum_factorial_div_log_add (n : ℕ) {a x : ℝ}
    (ha : 1 < a) (hx : 1 < x) :
    (∫ t in a..x, (Real.log t)⁻¹) =
      (∑ k ∈ Finset.range n,
        (k.factorial : ℝ) * (x / Real.log x ^ (k + 1) - a / Real.log a ^ (k + 1))) +
        (n.factorial : ℝ) * ∫ t in a..x, (Real.log t ^ (n + 1))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, add_assoc]
      congr 1
      rw [integral_inv_log_pow_eq_sub_add (n + 1) ha hx, mul_add, ← mul_assoc]
      congr 1
      rw [Nat.factorial_succ, Nat.cast_mul, mul_comm (n.factorial : ℝ)]

/-- **Asymptotic expansion of `Li` to any order `n`**:
`Li x = (x / log x) ∑_{k < n} k! / log x ^ k + O(x / log x ^ (n + 1))` as `x → ∞`. -/
theorem logIntegral_sub_sum_factorial_div_log_isBigO (n : ℕ) :
    (fun x : ℝ ↦ logIntegral x -
      (x / Real.log x) * ∑ k ∈ Finset.range n, (k.factorial : ℝ) / Real.log x ^ k) =O[atTop]
      fun x : ℝ ↦ x / Real.log x ^ (n + 1) := by
  let c : ℝ := -(∑ k ∈ Finset.range n, (k.factorial : ℝ) * (2 / Real.log 2 ^ (k + 1)))
  have hc : (fun _ : ℝ ↦ c) =O[atTop] fun x : ℝ ↦ x / Real.log x ^ (n + 1) := by
    simpa only [Real.rpow_natCast] using (isLittleO_const_div_log_rpow c (n + 1 : ℕ)).isBigO
  have hrem : (fun x : ℝ ↦ (n.factorial : ℝ) * ∫ t in (2 : ℝ)..x, (Real.log t ^ (n + 1))⁻¹)
      =O[atTop] fun x : ℝ ↦ x / Real.log x ^ (n + 1) :=
    (integral_inv_log_pow_isBigO (n + 1) one_lt_two).const_mul_left _
  refine (hc.add hrem).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [logIntegral_def, integral_inv_log_eq_sum_factorial_div_log_add n one_lt_two hx,
    Finset.mul_sum]
  have hsum : (∑ k ∈ Finset.range n,
      (k.factorial : ℝ) * (x / Real.log x ^ (k + 1) - 2 / Real.log 2 ^ (k + 1))) =
      (∑ k ∈ Finset.range n, x / Real.log x * ((k.factorial : ℝ) / Real.log x ^ k)) + c := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, c, sub_eq_add_neg]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [pow_succ']
    ring
  rw [hsum]
  ring

/-- **Asymptotic expansion of `li` to any order `n`**:
`li x = (x / log x) ∑_{k < n} k! / log x ^ k + O(x / log x ^ (n + 1))` as `x → ∞`. -/
theorem li_sub_sum_factorial_div_log_isBigO (n : ℕ) :
    (fun x : ℝ ↦ li x -
      (x / Real.log x) * ∑ k ∈ Finset.range n, (k.factorial : ℝ) / Real.log x ^ k) =O[atTop]
      fun x : ℝ ↦ x / Real.log x ^ (n + 1) := by
  have hc : (fun _ : ℝ ↦ li 2) =O[atTop] fun x : ℝ ↦ x / Real.log x ^ (n + 1) := by
    simpa only [Real.rpow_natCast] using (isLittleO_const_div_log_rpow (li 2) (n + 1 : ℕ)).isBigO
  refine ((logIntegral_sub_sum_factorial_div_log_isBigO n).add hc).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [li_eq_logIntegral_add_li_two hx]
  ring

/-- `li x ~ Li x` as `x → ∞`. -/
theorem li_isEquivalent_logIntegral : li ~[atTop] logIntegral := by
  rw [IsEquivalent]
  have hconst : (fun _ : ℝ ↦ li 2) =o[atTop] logIntegral :=
    (isLittleO_const_div_log (li 2)).trans_isEquivalent logIntegral_isEquivalent_div_log.symm
  refine hconst.congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [Pi.sub_apply, li_eq_logIntegral_add_li_two hx, add_sub_cancel_left]

/-- `li x ~ x / log x` as `x → ∞`. -/
theorem li_isEquivalent_div_log : li ~[atTop] fun x : ℝ ↦ x / Real.log x :=
  li_isEquivalent_logIntegral.trans logIntegral_isEquivalent_div_log

/-! ### Series truncation bounds and numerical enclosures of `li 2` -/

/-- For `y ≥ 0`, every finite partial sum bounds the exponential-integral series from below. -/
theorem sum_range_le_tsum_pow_div_mul_factorial {y : ℝ} (hy : 0 ≤ y) (N : ℕ) :
    (∑ n ∈ Finset.range N, y ^ (n + 1) / (((n : ℝ) + 1) * (n + 1).factorial)) ≤
      ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * (n + 1).factorial) :=
  (summable_pow_div_mul_factorial y).sum_le_tsum (Finset.range N) (fun _ _ ↦ by positivity)

/-- The exponential-integral series is monotone on `[0, ∞)`. -/
theorem tsum_pow_div_mul_factorial_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∑' n : ℕ, a ^ (n + 1) / (((n : ℝ) + 1) * (n + 1).factorial)) ≤
      ∑' n : ℕ, b ^ (n + 1) / (((n : ℝ) + 1) * (n + 1).factorial) := by
  refine (summable_pow_div_mul_factorial a).tsum_le_tsum (fun n ↦ ?_)
    (summable_pow_div_mul_factorial b)
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ ha hab _) (by positivity)

/-- Geometric-tail upper bound for the exponential-integral series: for `0 ≤ y < N + 2`, the tail
from index `N` onward is bounded by the `N`-th term divided by `1 - y / (N + 2)`. -/
theorem tsum_pow_div_mul_factorial_le_sum_range_add {y : ℝ} (hy : 0 ≤ y) {N : ℕ}
    (hyN : y < (N : ℝ) + 2) :
    (∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * (n + 1).factorial)) ≤
      (∑ n ∈ Finset.range N, y ^ (n + 1) / (((n : ℝ) + 1) * (n + 1).factorial)) +
        (y ^ (N + 1) / (((N : ℝ) + 1) * (N + 1).factorial)) /
          (1 - y / ((N : ℝ) + 2)) := by
  let f : ℕ → ℝ := fun n ↦ y ^ (n + 1) / (((n : ℝ) + 1) * (n + 1).factorial)
  let r : ℝ := y / ((N : ℝ) + 2)
  have hN2 : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  have hr0 : 0 ≤ r := div_nonneg hy hN2.le
  have hr1 : r < 1 := (div_lt_one hN2).mpr hyN
  rw [← (summable_pow_div_mul_factorial y).sum_add_tsum_nat_add N]
  refine add_le_add le_rfl ?_
  -- Step 1: Bound the shifted terms by a geometric progression of ratio `r = y / (N + 2)`.
  have hterm : ∀ m : ℕ, f (m + N) ≤ f N * r ^ m := by
    intro m
    induction m with
    | zero => simp [f]
    | succ m ih =>
        have hstep : f (m + 1 + N) ≤ f (m + N) * r := by
          have hk : m + 1 + N = (m + N) + 1 := by omega
          rw [hk]
          set k := m + N
          have hd2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
          have hratio : ((k : ℝ) + 1) / (((k : ℝ) + 2) * ((k : ℝ) + 2)) ≤
              1 / ((N : ℝ) + 2) := by
            rw [div_le_div_iff₀ (mul_pos hd2 hd2) hN2, one_mul]
            have h1 : (k : ℝ) + 1 ≤ (k : ℝ) + 2 := by linarith
            have h2 : (N : ℝ) + 2 ≤ (k : ℝ) + 2 := by
              have : N ≤ k := Nat.le_add_left N m
              exact_mod_cast Nat.add_le_add_right this 2
            exact mul_le_mul h1 h2 hN2.le hd2.le
          have hcast1 : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
          have hcast2 : ((k + 1 + 1 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
          dsimp only [f, r]
          rw [pow_succ _ (k + 1), Nat.factorial_succ (k + 1), Nat.cast_mul, hcast1, hcast2]
          calc y ^ (k + 1) * y / (((k : ℝ) + 2) * (((k : ℝ) + 2) * ((k + 1).factorial : ℝ)))
              = (y ^ (k + 1) / (((k : ℝ) + 1) * ((k + 1).factorial : ℝ))) *
                  (y * (((k : ℝ) + 1) / (((k : ℝ) + 2) * ((k : ℝ) + 2)))) := by
                field_simp
            _ ≤ (y ^ (k + 1) / (((k : ℝ) + 1) * ((k + 1).factorial : ℝ))) *
                  (y * (1 / ((N : ℝ) + 2))) := by
                gcongr
            _ = (y ^ (k + 1) / (((k : ℝ) + 1) * ((k + 1).factorial : ℝ))) *
                  (y / ((N : ℝ) + 2)) := by
                rw [mul_one_div]
        calc f (m + 1 + N) ≤ f (m + N) * r := hstep
          _ ≤ (f N * r ^ m) * r := mul_le_mul_of_nonneg_right ih hr0
          _ = f N * r ^ (m + 1) := by rw [pow_succ, mul_assoc]
  -- Step 2: Sum the dominating geometric series.
  have hsum_geom : Summable (fun m : ℕ ↦ f N * r ^ m) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left (f N)
  have htsum_le := ((summable_pow_div_mul_factorial y).comp_injective
    (add_left_injective N)).tsum_le_tsum hterm hsum_geom
  refine htsum_le.trans_eq ?_
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, ← div_eq_mul_inv]

/-- Lower numerical enclosure for the series term of `li 2`. -/
theorem le_tsum_log_two_pow_div_mul_factorial :
    (0.834461 : ℝ) ≤
      ∑' n : ℕ, Real.log 2 ^ (n + 1) / (((n : ℝ) + 1) * (n + 1).factorial) := by
  have hl2 : (0.69314718 : ℝ) ≤ Real.log 2 := le_trans (by norm_num) Real.log_two_gt_d9.le
  calc (0.834461 : ℝ)
      ≤ ∑ n ∈ Finset.range 8,
          (0.69314718 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * (n + 1).factorial) := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ ∑' n : ℕ, (0.69314718 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * (n + 1).factorial) :=
        sum_range_le_tsum_pow_div_mul_factorial (by norm_num) 8
    _ ≤ _ := tsum_pow_div_mul_factorial_mono (by norm_num) hl2

/-- Upper numerical enclosure for the series term of `li 2`. -/
theorem tsum_log_two_pow_div_mul_factorial_le :
    (∑' n : ℕ, Real.log 2 ^ (n + 1) / (((n : ℝ) + 1) * (n + 1).factorial)) ≤ 0.8344611 := by
  have hl2 : Real.log 2 ≤ 0.69314719 := le_trans Real.log_two_lt_d9.le (by norm_num)
  calc (∑' n : ℕ, Real.log 2 ^ (n + 1) / (((n : ℝ) + 1) * (n + 1).factorial))
      ≤ ∑' n : ℕ, (0.69314719 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * (n + 1).factorial) :=
        tsum_pow_div_mul_factorial_mono (Real.log_pos one_lt_two).le hl2
    _ ≤ (∑ n ∈ Finset.range 8,
          (0.69314719 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * (n + 1).factorial)) +
          ((0.69314719 : ℝ) ^ (8 + 1) / (((8 : ℕ) + 1) * (8 + 1).factorial)) /
            (1 - (0.69314719 : ℝ) / ((8 : ℕ) + 2)) :=
        tsum_pow_div_mul_factorial_le_sum_range_add (by norm_num) (by norm_num)
    _ ≤ 0.8344611 := by norm_num [Finset.sum_range_succ, Nat.factorial]

/-- Lower numerical enclosure for `log (log 2)`. -/
theorem le_log_log_two : (-0.366513 : ℝ) ≤ Real.log (Real.log 2) := by
  have hl2 : (0.69314718 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hmono : Real.log 0.69314718 ≤ Real.log (Real.log 2) :=
    Real.log_le_log (by norm_num) hl2.le
  let x : ℝ := (1 - 0.69314718) / (1 + 0.69314718)
  have hx0 : 0 ≤ x := by norm_num [x]
  have hx1 : x < 1 := by norm_num [x]
  have hratio : (1 + x) / (1 - x) = (0.69314718 : ℝ)⁻¹ := by norm_num [x]
  have hup := Real.log_div_le_sum_range_add hx0 hx1 5
  rw [hratio, Real.log_inv] at hup
  have hnum : (∑ i ∈ Finset.range 5, x ^ (2 * i + 1) / (2 * i + 1)) +
      x ^ (2 * 5 + 1) / (1 - x ^ 2) ≤ 0.366513 / 2 := by
    norm_num [x, Finset.sum_range_succ]
  linarith [hnum]

/-- Upper numerical enclosure for `log (log 2)`. -/
theorem log_log_two_le : Real.log (Real.log 2) ≤ -0.366512 := by
  have hl2 : Real.log 2 < 0.69314719 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hmono : Real.log (Real.log 2) ≤ Real.log 0.69314719 :=
    Real.log_le_log (Real.log_pos one_lt_two) hl2.le
  let x : ℝ := (1 - 0.69314719) / (1 + 0.69314719)
  have hx0 : 0 ≤ x := by norm_num [x]
  have hx1 : x < 1 := by norm_num [x]
  have hratio : (1 + x) / (1 - x) = (0.69314719 : ℝ)⁻¹ := by norm_num [x]
  have hlo := Real.sum_range_le_log_div hx0 hx1 5
  rw [hratio, Real.log_inv] at hlo
  have hnum : 0.366512 / 2 ≤ ∑ i ∈ Finset.range 5, x ^ (2 * i + 1) / (2 * i + 1) := by
    norm_num [x, Finset.sum_range_succ]
  linarith [hnum]

/-- Unconditional lower enclosure for `li 2 - γ`. -/
theorem le_li_two_sub_eulerMascheroniConstant :
    (0.467948 : ℝ) ≤ li 2 - Real.eulerMascheroniConstant := by
  rw [li_def]
  linarith [le_log_log_two, le_tsum_log_two_pow_div_mul_factorial]

/-- Unconditional upper enclosure for `li 2 - γ`. -/
theorem li_two_sub_eulerMascheroniConstant_le :
    li 2 - Real.eulerMascheroniConstant ≤ 0.467950 := by
  rw [li_def]
  linarith [log_log_two_le, tsum_log_two_pow_div_mul_factorial_le]

/-- Unconditional lower bound `0.96 < li 2`, from Mathlib's `1 / 2 < γ`. -/
theorem li_two_gt : (0.96 : ℝ) < li 2 := by
  linarith [Real.one_half_lt_eulerMascheroniConstant, le_li_two_sub_eulerMascheroniConstant]

/-- Unconditional upper bound `li 2 < 1.14`, from Mathlib's `γ < 2 / 3`. -/
theorem li_two_lt : li 2 < 1.14 := by
  linarith [Real.eulerMascheroniConstant_lt_two_thirds, li_two_sub_eulerMascheroniConstant_le]

/-- Tight lower enclosure `1.0451 ≤ li 2` given the 9-digit enclosure of Euler's constant. -/
theorem le_li_two_of_abs_eulerMascheroniConstant_sub_lt
    (hγ : |Real.eulerMascheroniConstant - 0.5772156649| < 1 / 10 ^ 9) :
    (1.0451 : ℝ) ≤ li 2 := by
  have hlo := (abs_lt.mp hγ).1
  linarith [le_li_two_sub_eulerMascheroniConstant]

/-- Tight upper enclosure `li 2 ≤ 1.0452` given the 9-digit enclosure of Euler's constant. -/
theorem li_two_le_of_abs_eulerMascheroniConstant_sub_lt
    (hγ : |Real.eulerMascheroniConstant - 0.5772156649| < 1 / 10 ^ 9) :
    li 2 ≤ 1.0452 := by
  have hhi := (abs_lt.mp hγ).2
  linarith [li_two_sub_eulerMascheroniConstant_le]

/-! ### The difference `Li x - x / log x` -/

/-- The derivative of `x ↦ Li x - x / log x` on `(1, ∞)` is `(log x ^ 2)⁻¹`. -/
theorem hasDerivAt_logIntegral_sub_div_log {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun t : ℝ ↦ logIntegral t - t / Real.log t) (Real.log x ^ 2)⁻¹ x := by
  have hd := (hasDerivAt_logIntegral hx).sub
    (hasDerivAt_div_log_pow 1 (Real.log_pos hx).ne')
  simp only [Pi.sub_def, pow_one] at hd
  exact hd.congr_deriv (by norm_num)

/-- `x ↦ Li x - x / log x` is strictly increasing on `(1, ∞)`. -/
theorem strictMonoOn_logIntegral_sub_div_log :
    StrictMonoOn (fun x : ℝ ↦ logIntegral x - x / Real.log x) (Ioi 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 1)
    (fun x hx ↦ (hasDerivAt_logIntegral_sub_div_log hx).continuousAt.continuousWithinAt)
    fun x hx ↦ ?_
  rw [interior_Ioi] at hx
  rw [(hasDerivAt_logIntegral_sub_div_log hx).deriv]
  exact inv_pos.mpr (pow_pos (Real.log_pos hx) 2)

/-- Lower bound on the increment of `Li x - x / log x` across `[a, x] ⊂ (1, ∞)`:
`(x - a) / log x ^ 2 ≤ (Li x - x / log x) - (Li a - a / log a)`. -/
theorem div_log_sq_le_sub_logIntegral_sub_div_log {a x : ℝ} (ha : 1 < a) (hax : a ≤ x) :
    (x - a) / Real.log x ^ 2 ≤
      (logIntegral x - x / Real.log x) - (logIntegral a - a / Real.log a) := by
  have hx1 : 1 < x := ha.trans_le hax
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hasDerivAt_logIntegral_sub_div_log (by
      rw [uIcc_of_le hax] at ht
      exact ha.trans_le ht.1))
    (intervalIntegrable_inv_log_pow 2 ha hx1)
  rw [← hFTC]
  exact le_integral_inv_log_pow 2 ha hax

/-- Explicit lower bound for `Li x - x / log x` when `2 ≤ x`. -/
theorem le_logIntegral_sub_div_log {x : ℝ} (hx : 2 ≤ x) :
    x / Real.log x ^ 2 - 2 / Real.log 2 - 2 / Real.log 2 ^ 2 ≤
      logIntegral x - x / Real.log x := by
  have hinc := div_log_sq_le_sub_logIntegral_sub_div_log one_lt_two hx
  rw [logIntegral_two, zero_sub, sub_neg_eq_add, sub_div] at hinc
  have hsq : Real.log 2 ^ 2 ≤ Real.log x ^ 2 :=
    pow_le_pow_left₀ (Real.log_pos one_lt_two).le (Real.log_le_log two_pos hx) 2
  have hdiv : 2 / Real.log x ^ 2 ≤ 2 / Real.log 2 ^ 2 :=
    div_le_div_of_nonneg_left zero_le_two (pow_pos (Real.log_pos one_lt_two) 2) hsq
  linarith

/-- Strict explicit lower bound for `Li x - x / log x` when `2 < x`. -/
theorem lt_logIntegral_sub_div_log {x : ℝ} (hx : 2 < x) :
    x / Real.log x ^ 2 - 2 / Real.log 2 - 2 / Real.log 2 ^ 2 <
      logIntegral x - x / Real.log x := by
  have hinc := div_log_sq_le_sub_logIntegral_sub_div_log one_lt_two hx.le
  rw [logIntegral_two, zero_sub, sub_neg_eq_add, sub_div] at hinc
  have hsq : Real.log 2 ^ 2 < Real.log x ^ 2 :=
    pow_lt_pow_left₀ (Real.log_lt_log two_pos hx) (Real.log_pos one_lt_two).le two_ne_zero
  have hdiv : 2 / Real.log x ^ 2 < 2 / Real.log 2 ^ 2 :=
    div_lt_div_of_pos_left two_pos (pow_pos (Real.log_pos one_lt_two) 2) hsq
  linarith

/-- Explicit upper bound for `Li x - x / log x` when `2 ≤ x`. -/
theorem logIntegral_sub_div_log_lt {x : ℝ} (hx : 2 ≤ x) :
    logIntegral x - x / Real.log x <
      x / Real.log x ^ 2 + 2 * √x / Real.log 2 ^ 3 + 16 * x / Real.log x ^ 3 - 2 / Real.log 2 := by
  have h1 := logIntegral_eq_div_log_sub_add hx
  have h2 := integral_inv_log_pow_lt_div_add 2 one_lt_two hx
  norm_num at h2
  have hring : x / Real.log x ^ 2 + 2 * (√x / Real.log 2 ^ 3 + 8 * x / Real.log x ^ 3) =
      x / Real.log x ^ 2 + 2 * √x / Real.log 2 ^ 3 + 16 * x / Real.log x ^ 3 := by ring
  linarith

/-- Series formula for `Li a` (`a > 1`) in which Euler's constant `γ` cancels out:
`Li a = log (log a / log 2) + S(log a) - S(log 2)`. -/
theorem logIntegral_eq_log_div_add_tsum_sub {a : ℝ} (ha : 1 < a) :
    logIntegral a =
      Real.log (Real.log a / Real.log 2) +
        (∑' n : ℕ, Real.log a ^ (n + 1) / (((n : ℝ) + 1) * (n + 1).factorial)) -
        ∑' n : ℕ, Real.log 2 ^ (n + 1) / (((n : ℝ) + 1) * (n + 1).factorial) := by
  rw [logIntegral_eq_li_sub_li_two ha, li_def, li_def,
    Real.log_div (Real.log_pos ha).ne' (Real.log_pos one_lt_two).ne']
  ring

/-- Elementary upper bound `log (u / log 2) ≤ u / (e * log 2)` for `u > 0`, from
`log (u / (e * log 2)) ≤ u / (e * log 2) - 1`. -/
private theorem log_div_log_two_le {u : ℝ} (hu : 0 < u) :
    Real.log (u / Real.log 2) ≤ u / (Real.exp 1 * Real.log 2) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have h := Real.log_le_sub_one_of_pos (div_pos hu (mul_pos he hl2))
  have hlog : Real.log (u / (Real.exp 1 * Real.log 2)) = Real.log (u / Real.log 2) - 1 := by
    rw [Real.log_div hu.ne' (mul_pos he hl2).ne', Real.log_mul he.ne' hl2.ne', Real.log_exp,
      Real.log_div hu.ne' hl2.ne']
    ring
  linarith

/-- Elementary lower bound `2 - e * log 2 / u ≤ log (u / log 2)` for `u > 0`, from
`log (e * log 2 / u) ≤ e * log 2 / u - 1`. -/
private theorem le_log_div_log_two {u : ℝ} (hu : 0 < u) :
    2 - Real.exp 1 * Real.log 2 / u ≤ Real.log (u / Real.log 2) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have h := Real.log_le_sub_one_of_pos (div_pos (mul_pos he hl2) hu)
  have hlog : Real.log (Real.exp 1 * Real.log 2 / u) = 1 - Real.log (u / Real.log 2) := by
    rw [Real.log_div (mul_pos he hl2).ne' hu.ne', Real.log_mul he.ne' hl2.ne', Real.log_exp,
      Real.log_div hu.ne' hl2.ne']
    ring
  linarith

/-- Enclosure `1.883989 < log 6.5797 < 1.883990`. -/
private theorem log_65797_bounds :
    (1.883989 : ℝ) < Real.log 6.5797 ∧ Real.log 6.5797 < 1.883990 := by
  have hsplit : Real.log (6.5797 : ℝ) = Real.log 2 + Real.log 3 + Real.log (6.5797 / 6) := by
    rw [← Real.log_mul two_ne_zero (by norm_num), ← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  let x : ℝ := (6.5797 / 6 - 1) / (6.5797 / 6 + 1)
  have hx0 : 0 ≤ x := by norm_num [x]
  have hx1 : x < 1 := by norm_num [x]
  have hratio : (1 + x) / (1 - x) = (6.5797 : ℝ) / 6 := by norm_num [x]
  have hlo := Real.sum_range_le_log_div hx0 hx1 2
  have hhi := Real.log_div_le_sum_range_add hx0 hx1 2
  rw [hratio] at hlo hhi
  have hnum_lo : (0.09222959 : ℝ) / 2 ≤ ∑ i ∈ Finset.range 2, x ^ (2 * i + 1) / (2 * i + 1) := by
    norm_num [x, Finset.sum_range_succ]
  have hnum_hi : (∑ i ∈ Finset.range 2, x ^ (2 * i + 1) / (2 * i + 1)) +
      x ^ (2 * 2 + 1) / (1 - x ^ 2) ≤ 0.09223002 / 2 := by
    norm_num [x, Finset.sum_range_succ]
  constructor <;>
    linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, Real.log_three_gt_d9, Real.log_three_lt_d9,
      hnum_lo, hnum_hi]

/-- Enclosure `1.884004 < log 6.5798 < 1.884005`. -/
private theorem log_65798_bounds :
    (1.884004 : ℝ) < Real.log 6.5798 ∧ Real.log 6.5798 < 1.884005 := by
  have hsplit : Real.log (6.5798 : ℝ) = Real.log 2 + Real.log 3 + Real.log (6.5798 / 6) := by
    rw [← Real.log_mul two_ne_zero (by norm_num), ← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  let x : ℝ := (6.5798 / 6 - 1) / (6.5798 / 6 + 1)
  have hx0 : 0 ≤ x := by norm_num [x]
  have hx1 : x < 1 := by norm_num [x]
  have hratio : (1 + x) / (1 - x) = (6.5798 : ℝ) / 6 := by norm_num [x]
  have hlo := Real.sum_range_le_log_div hx0 hx1 2
  have hhi := Real.log_div_le_sum_range_add hx0 hx1 2
  rw [hratio] at hlo hhi
  have hnum_lo : (0.09224479 : ℝ) / 2 ≤ ∑ i ∈ Finset.range 2, x ^ (2 * i + 1) / (2 * i + 1) := by
    norm_num [x, Finset.sum_range_succ]
  have hnum_hi : (∑ i ∈ Finset.range 2, x ^ (2 * i + 1) / (2 * i + 1)) +
      x ^ (2 * 2 + 1) / (1 - x ^ 2) ≤ 0.09224522 / 2 := by
    norm_num [x, Finset.sum_range_succ]
  constructor <;>
    linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, Real.log_three_gt_d9, Real.log_three_lt_d9,
      hnum_lo, hnum_hi]

/-- `Li x - x / log x < 0` for all `x ∈ (1, 6.5797]`. -/
theorem logIntegral_sub_div_log_neg {x : ℝ} (hx1 : 1 < x) (hx : x ≤ 6.5797) :
    logIntegral x - x / Real.log x < 0 := by
  suffices h0 : logIntegral (6.5797 : ℝ) - 6.5797 / Real.log 6.5797 < 0 by
    rcases hx.eq_or_lt with rfl | hlt
    · exact h0
    · exact (strictMonoOn_logIntegral_sub_div_log hx1 (by norm_num : (1 : ℝ) < 6.5797) hlt).trans
        h0
  have ⟨hlo, hhi⟩ := log_65797_bounds
  have hlpos : 0 < Real.log 6.5797 := by linarith
  have hlogratio : Real.log (Real.log 6.5797 / Real.log 2) ≤ 0.999905 := by
    have h1 := log_div_log_two_le hlpos
    have hdenom : (2.7182818283 : ℝ) * 0.6931471803 ≤ Real.exp 1 * Real.log 2 :=
      mul_le_mul Real.exp_one_gt_d9.le Real.log_two_gt_d9.le (by norm_num) (Real.exp_pos 1).le
    have h2 : Real.log 6.5797 / (Real.exp 1 * Real.log 2) ≤
        1.883990 / (2.7182818283 * 0.6931471803) :=
      div_le_div₀ (by norm_num) hhi.le (by norm_num) hdenom
    linarith
  have hS : (∑' n : ℕ, Real.log 6.5797 ^ (n + 1) / (((n : ℝ) + 1) * (n + 1).factorial)) ≤
      3.326982 := by
    calc (∑' n : ℕ, Real.log 6.5797 ^ (n + 1) / (((n : ℝ) + 1) * (n + 1).factorial))
        ≤ ∑' n : ℕ, (1.883990 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * (n + 1).factorial) :=
          tsum_pow_div_mul_factorial_mono hlpos.le hhi.le
      _ ≤ (∑ n ∈ Finset.range 10,
            (1.883990 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * (n + 1).factorial)) +
            ((1.883990 : ℝ) ^ (10 + 1) / (((10 : ℕ) + 1) * (10 + 1).factorial)) /
              (1 - (1.883990 : ℝ) / ((10 : ℕ) + 2)) :=
          tsum_pow_div_mul_factorial_le_sum_range_add (by norm_num) (by norm_num)
      _ ≤ 3.326982 := by norm_num [Finset.sum_range_succ, Nat.factorial]
  have hdiv : (3.492428 : ℝ) ≤ 6.5797 / Real.log 6.5797 := by
    rw [le_div_iff₀ hlpos]
    nlinarith
  rw [logIntegral_eq_log_div_add_tsum_sub (by norm_num : (1 : ℝ) < 6.5797)]
  linarith [le_tsum_log_two_pow_div_mul_factorial]

/-- `0 < Li x - x / log x` for all `x ≥ 6.5798`. -/
theorem logIntegral_sub_div_log_pos {x : ℝ} (hx : (6.5798 : ℝ) ≤ x) :
    0 < logIntegral x - x / Real.log x := by
  suffices h0 : 0 < logIntegral (6.5798 : ℝ) - 6.5798 / Real.log 6.5798 by
    rcases hx.eq_or_lt with rfl | hlt
    · exact h0
    · exact h0.trans (strictMonoOn_logIntegral_sub_div_log
        (mem_Ioi.mpr (by norm_num : (1 : ℝ) < 6.5798))
        (mem_Ioi.mpr (by linarith)) hlt)
  have ⟨hlo, hhi⟩ := log_65798_bounds
  have hlpos : 0 < Real.log 6.5798 := by linarith
  have hlogratio : (0.999912 : ℝ) ≤ Real.log (Real.log 6.5798 / Real.log 2) := by
    have h1 := le_log_div_log_two hlpos
    have hnum : Real.exp 1 * Real.log 2 ≤ (2.7182818286 : ℝ) * 0.6931471808 :=
      mul_le_mul Real.exp_one_lt_d9.le Real.log_two_lt_d9.le
        (Real.log_pos one_lt_two).le (by norm_num)
    have h2 : Real.exp 1 * Real.log 2 / Real.log 6.5798 ≤
        (2.7182818286 * 0.6931471808) / 1.884004 :=
      div_le_div₀ (by norm_num) hnum (by norm_num) hlo.le
    linarith
  have hS : (3.327019 : ℝ) ≤
      ∑' n : ℕ, Real.log 6.5798 ^ (n + 1) / (((n : ℝ) + 1) * (n + 1).factorial) := by
    calc (3.327019 : ℝ)
        ≤ ∑ n ∈ Finset.range 10,
            (1.884004 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * (n + 1).factorial) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ ∑' n : ℕ, (1.884004 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * (n + 1).factorial) :=
          sum_range_le_tsum_pow_div_mul_factorial (by norm_num) 10
      _ ≤ _ := tsum_pow_div_mul_factorial_mono (by norm_num) hlo.le
  have hdiv : 6.5798 / Real.log 6.5798 ≤ 3.492456 := by
    rw [div_le_iff₀ hlpos]
    nlinarith
  rw [logIntegral_eq_log_div_add_tsum_sub (by norm_num : (1 : ℝ) < 6.5798)]
  linarith [tsum_log_two_pow_div_mul_factorial_le]

/-- Every zero of `Li x - x / log x` in `(1, ∞)` lies in `(6.5797, 6.5798)`. -/
theorem logIntegral_sub_div_log_eq_zero_mem_Ioo {x : ℝ} (hx1 : 1 < x)
    (hx : logIntegral x - x / Real.log x = 0) :
    x ∈ Ioo (6.5797 : ℝ) 6.5798 := by
  refine ⟨?_, ?_⟩
  · by_contra h
    push Not at h
    linarith [logIntegral_sub_div_log_neg hx1 h]
  · by_contra h
    push Not at h
    linarith [logIntegral_sub_div_log_pos h]

/-- `Li x - x / log x` has a unique zero in `(1, ∞)`. -/
theorem existsUnique_logIntegral_sub_div_log_eq_zero :
    ∃! x ∈ Ioi (1 : ℝ), logIntegral x - x / Real.log x = 0 := by
  let g : ℝ → ℝ := fun x ↦ logIntegral x - x / Real.log x
  have hcont : ContinuousOn g (Icc (6.5797 : ℝ) 6.5798) := fun t ht ↦
    (hasDerivAt_logIntegral_sub_div_log (by linarith [ht.1])).continuousAt.continuousWithinAt
  have hneg : g 6.5797 < 0 := logIntegral_sub_div_log_neg (by norm_num) le_rfl
  have hpos : 0 < g 6.5798 := logIntegral_sub_div_log_pos le_rfl
  obtain ⟨x₀, hx₀_mem, hx₀_eq⟩ := intermediate_value_Icc (by norm_num : (6.5797 : ℝ) ≤ 6.5798)
    hcont ⟨hneg.le, hpos.le⟩
  have hx₀_gt : (1 : ℝ) < x₀ := by linarith [hx₀_mem.1]
  refine ⟨x₀, ⟨mem_Ioi.mpr hx₀_gt, hx₀_eq⟩, fun y ⟨hy1, hyeq⟩ ↦ ?_⟩
  exact strictMonoOn_logIntegral_sub_div_log.injOn hy1 (mem_Ioi.mpr hx₀_gt)
    (hyeq.trans hx₀_eq.symm)

/-- For every `6.5798 ≤ a ≤ x`, `(x - a) / log x ^ 2 < Li x - x / log x`.
In particular, at `a = 6.58`, `(x - 6.58) / log x ^ 2 ≤ Li x - x / log x` for all `x ≥ 6.58`
(Fiori–Kadiri–Swidinsky, Lemma 20). -/
theorem sub_div_log_sq_lt_logIntegral_sub_div_log {a x : ℝ}
    (ha : (6.5798 : ℝ) ≤ a) (hax : a ≤ x) :
    (x - a) / Real.log x ^ 2 < logIntegral x - x / Real.log x := by
  have hpos := logIntegral_sub_div_log_pos ha
  have hinc := div_log_sq_le_sub_logIntegral_sub_div_log (by linarith) hax
  linarith

end TauCeti.Real
