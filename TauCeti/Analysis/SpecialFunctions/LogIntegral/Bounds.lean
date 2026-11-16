/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.LogIntegral.Unoffset
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Explicit bounds and asymptotic expansion for the logarithmic integral

This file establishes the quantitative and asymptotic properties of the unoffset logarithmic
integral `TauCeti.Real.li` and the offset logarithmic integral `TauCeti.Real.logIntegral` (`Li`):

* **Explicit integrals of reciprocal log powers**: for every real `k`, integration by parts yields
  `∫ t in a..b, (log t ^ k)⁻¹ =`
  `b / log b ^ k - a / log a ^ k + k * ∫ t in a..b, (log t ^ (k + 1))⁻¹`;
  for `k ≥ 0` and `x ≥ 2`, splitting at `√x` bounds `∫ t in 2..x, (log t ^ k)⁻¹` by
  `√x / log 2 ^ k + 2 ^ k * x / log x ^ k`, with natural-power specializations covering arbitrary
  exponents `n : ℕ`.
* **Asymptotic expansion**: repeated integration by parts gives
  `li x - (x / log x) * ∑ k ∈ range n, k! / log x ^ k = O(x / log x ^ (n + 1))` as `x → ∞`,
  together with `li ~ Li ~ x / log x`.
* **Numerical enclosures of `li 2`**: explicit bounds on the entire-part series
  `∑_{n ≥ 1} (log 2)^n / (n * n!) ∈ [0.8344605, 0.8344615]` and
  `log (log 2) ∈ [-0.366513, -0.366512]` yield the unconditional enclosure `0.96 < li 2 < 1.14`
  and, given `|γ - 0.5772156649| < 10⁻⁹`, the tight enclosure `1.0451 ≤ li 2 ≤ 1.0452`.
* **Bounds and unique zero of `Li x - x / log x`**: strict monotonicity on `(1, ∞)`, explicit
  two-sided bounds for `x ≥ 2`, localization of the unique zero in `(6.5797, 6.5798)`, sign bounds
  away from `(6.5797, 6.5798)`, and Fiori–Kadiri–Swidinsky's lower bound
  `(x - 6.58) / log x ^ 2 ≤ Li x - x / log x` for `x ≥ 6.58`.

## Main declarations

* `TauCeti.Real.integral_inv_log_rpow_eq_sub_add`, `TauCeti.Real.integral_inv_log_rpow_le_sqrt_add`,
  `TauCeti.Real.integral_inv_log_rpow_lt_div_add` — integration by parts and explicit upper bounds
  for `∫₂ˣ dt / log^k t`.
* `TauCeti.Real.logIntegral_eq_sum_add_integral`, `TauCeti.Real.li_sub_sum_isBigO`,
  `TauCeti.Real.li_isEquivalent_logIntegral`, `TauCeti.Real.li_isEquivalent_div_log` — asymptotic
  expansion and prime-number-theorem equivalences for `li`.
* `TauCeti.Real.lt_li_two`, `TauCeti.Real.li_two_lt`,
  `TauCeti.Real.le_li_two_of_abs_eulerMascheroniConstant_sub_lt`,
  `TauCeti.Real.li_two_le_of_abs_eulerMascheroniConstant_sub_lt` — unconditional and conditional
  enclosures of `li 2`.
* `TauCeti.Real.strictMonoOn_logIntegral_sub_div_log`, `TauCeti.Real.le_logIntegral_sub_div_log`,
  `TauCeti.Real.logIntegral_sub_div_log_lt`, `TauCeti.Real.existsUnique_logIntegral_eq_div_log`,
  `TauCeti.Real.existsUnique_logIntegral_eq_div_log_Ioo`,
  `TauCeti.Real.logIntegral_sub_div_log_neg`, `TauCeti.Real.logIntegral_sub_div_log_pos`,
  `TauCeti.Real.div_log_sq_le_logIntegral_sub_div_log` — monotonicity, bounds, unique zero, and
  Fiori–Kadiri–Swidinsky Lemma 20 for `Li x - x / log x`.

## References

* F. W. J. Olver et al., *NIST Digital Library of Mathematical Functions*, §6.2 and §6.12.
* A. Fiori, H. Kadiri, and J. Swidinsky, *Sharper bounds for the Chebyshev function ψ(x)*,
  J. Math. Anal. Appl. 527 (2023), 127426, Lemma 20.
-/

public section

namespace TauCeti.Real

open Asymptotics Filter MeasureTheory Set
open scoped Topology Nat

/-! ### Explicit integrals of reciprocal real powers of `log` -/

/-- Reciprocal real powers of `log` are continuous on `(1, ∞)`. -/
theorem continuousOn_inv_log_rpow (k : ℝ) :
    ContinuousOn (fun t : ℝ ↦ (Real.log t ^ k)⁻¹) (Ioi 1) := by
  have hlog : ContinuousOn Real.log (Ioi 1) :=
    Real.continuousOn_log.mono fun t ht ↦ ne_of_gt (zero_lt_one.trans ht)
  have hrpow : ContinuousOn (fun t : ℝ ↦ Real.log t ^ k) (Ioi 1) :=
    hlog.rpow_const fun t ht ↦ Or.inl (Real.log_pos ht).ne'
  exact hrpow.inv₀ fun t ht ↦ (Real.rpow_pos_of_pos (Real.log_pos ht) k).ne'

/-- Reciprocal real powers of `log` are interval integrable on any interval to the right of `1`. -/
theorem intervalIntegrable_inv_log_rpow (k : ℝ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun t : ℝ ↦ (Real.log t ^ k)⁻¹) volume a b := by
  refine ((continuousOn_inv_log_rpow k).mono fun t ht ↦ ?_).intervalIntegrable
  rcases mem_uIcc.mp ht with ht | ht
  · exact ha.trans_le ht.1
  · exact hb.trans_le ht.1

/-- Integration by parts for `∫ t in a..b, (log t ^ k)⁻¹` with any real exponent `k` and
endpoints `a, b > 1`. -/
theorem integral_inv_log_rpow_eq_sub_add (k : ℝ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    (∫ t in a..b, (Real.log t ^ k)⁻¹) =
      b / Real.log b ^ k - a / Real.log a ^ k + k * ∫ t in a..b, (Real.log t ^ (k + 1))⁻¹ := by
  have hi := intervalIntegrable_inv_log_rpow k ha hb
  have hi1 := intervalIntegrable_inv_log_rpow (k + 1) ha hb
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hasDerivAt_div_log_rpow k (Real.log_pos (by
      rcases mem_uIcc.mp ht with ht | ht
      · exact ha.trans_le ht.1
      · exact hb.trans_le ht.1)))
    (hi.sub (hi1.const_mul k))
  rw [intervalIntegral.integral_sub hi (hi1.const_mul k),
    intervalIntegral.integral_const_mul] at hFTC
  exact sub_eq_iff_eq_add.mp hFTC

/-- Monotonicity upper bound `∫ t in a..b, (log t ^ k)⁻¹ ≤ (b - a) / log a ^ k` for
`k ≥ 0`. -/
theorem integral_inv_log_rpow_le {k : ℝ} (hk : 0 ≤ k) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, (Real.log t ^ k)⁻¹ ≤ (b - a) / Real.log a ^ k := by
  have hla : 0 < Real.log a := Real.log_pos ha
  have hb : 1 < b := ha.trans_le hab
  have hmono := intervalIntegral.integral_mono_on hab (intervalIntegrable_inv_log_rpow k ha hb)
    (g := fun _ ↦ (Real.log a ^ k)⁻¹) intervalIntegrable_const fun t ht ↦
      inv_anti₀ (Real.rpow_pos_of_pos hla k)
        (Real.rpow_le_rpow hla.le (Real.log_le_log (by linarith) ht.1) hk)
  simpa [smul_eq_mul, div_eq_mul_inv] using hmono

/-- Monotonicity lower bound `(b - a) / log b ^ k ≤ ∫ t in a..b, (log t ^ k)⁻¹` for
`k ≥ 0`. -/
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

/-- Explicit upper bound `∫ t in 2..x, (log t ^ k)⁻¹ ≤ √x / log 2 ^ k + 2 ^ k * x / log x ^ k`
for every real `k ≥ 0` and `x ≥ 2`. -/
theorem integral_inv_log_rpow_le_sqrt_add {k : ℝ} (hk : 0 ≤ k) {x : ℝ} (hx : 2 ≤ x) :
    (∫ t in (2 : ℝ)..x, (Real.log t ^ k)⁻¹) ≤
      √x / Real.log 2 ^ k + 2 ^ k * x / Real.log x ^ k := by
  have hx0 : 0 < x := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  rcases le_or_gt 4 x with h4 | h4
  · have hsq : 2 ≤ √x := by nlinarith [Real.sq_sqrt hx0.le, Real.sqrt_nonneg x]
    have hle : √x ≤ x := by
      rw [Real.sqrt_le_self_iff]
      exact Or.inr (by linarith)
    have hsplit : (∫ t in (2 : ℝ)..x, (Real.log t ^ k)⁻¹) =
        (∫ t in (2 : ℝ)..√x, (Real.log t ^ k)⁻¹) +
          ∫ t in √x..x, (Real.log t ^ k)⁻¹ :=
      (intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_inv_log_rpow k one_lt_two (by linarith))
        (intervalIntegrable_inv_log_rpow k (by linarith) (by linarith))).symm
    have hb₁ : (∫ t in (2 : ℝ)..√x, (Real.log t ^ k)⁻¹) ≤ √x / Real.log 2 ^ k := by
      refine (integral_inv_log_rpow_le hk one_lt_two hsq).trans ?_
      gcongr
      linarith
    have hb₂ : (∫ t in √x..x, (Real.log t ^ k)⁻¹) ≤ 2 ^ k * x / Real.log x ^ k := by
      refine (integral_inv_log_rpow_le hk (by linarith) hle).trans ?_
      rw [Real.log_sqrt hx0.le, Real.div_rpow hlogx.le zero_le_two, div_div_eq_mul_div,
        mul_comm (x - √x)]
      gcongr
      linarith [Real.sqrt_nonneg x]
    rw [hsplit]
    linarith
  · have hlog_half : Real.log x / 2 ≤ Real.log 2 := by
      have h : Real.log x ≤ Real.log (2 ^ 2) :=
        Real.log_le_log hx0 (by norm_num; exact h4.le)
      rw [Real.log_pow] at h
      norm_num at h
      linarith
    have hb : (∫ t in (2 : ℝ)..x, (Real.log t ^ k)⁻¹) ≤ 2 ^ k * x / Real.log x ^ k := by
      refine (integral_inv_log_rpow_le hk one_lt_two hx).trans ?_
      have hrpow_le : (Real.log x / 2) ^ k ≤ Real.log 2 ^ k :=
        Real.rpow_le_rpow (by positivity) hlog_half hk
      have hdiv : (x - 2) / Real.log 2 ^ k ≤ (x - 2) / (Real.log x / 2) ^ k :=
        div_le_div_of_nonneg_left (by linarith) (Real.rpow_pos_of_pos (by positivity) k) hrpow_le
      refine hdiv.trans ?_
      rw [Real.div_rpow hlogx.le zero_le_two, div_div_eq_mul_div, mul_comm (x - 2)]
      gcongr
      linarith
    have hnn : 0 ≤ √x / Real.log 2 ^ k :=
      div_nonneg (Real.sqrt_nonneg x) (Real.rpow_pos_of_pos hlog2 k).le
    linarith

/-- Explicit strict upper bound for `∫ t in 2..x, (log t ^ k)⁻¹` obtained by one integration by
parts followed by `integral_inv_log_rpow_le_sqrt_add`, for every real `k > 0` and `x ≥ 2`. -/
theorem integral_inv_log_rpow_lt_div_add {k : ℝ} (hk : 0 < k) {x : ℝ} (hx : 2 ≤ x) :
    (∫ t in (2 : ℝ)..x, (Real.log t ^ k)⁻¹) <
      x / Real.log x ^ k +
        k * (√x / Real.log 2 ^ (k + 1) + 2 ^ (k + 1) * x / Real.log x ^ (k + 1)) := by
  rw [integral_inv_log_rpow_eq_sub_add k one_lt_two (by linarith)]
  have h2pos : 0 < 2 / Real.log 2 ^ k :=
    div_pos two_pos (Real.rpow_pos_of_pos (Real.log_pos one_lt_two) k)
  have hrem := integral_inv_log_rpow_le_sqrt_add (k := k + 1) (by linarith) hx
  nlinarith

/-- Natural-power specialization of `integral_inv_log_rpow_le_sqrt_add`. -/
theorem integral_inv_log_pow_le_sqrt_add (n : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    (∫ t in (2 : ℝ)..x, (Real.log t ^ n)⁻¹) ≤
      √x / Real.log 2 ^ n + 2 ^ n * x / Real.log x ^ n := by
  simpa only [Real.rpow_natCast] using
    integral_inv_log_rpow_le_sqrt_add (k := (n : ℝ)) (Nat.cast_nonneg n) hx

/-- Natural-power specialization of `integral_inv_log_rpow_lt_div_add`. -/
theorem integral_inv_log_pow_lt_div_add {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 2 ≤ x) :
    (∫ t in (2 : ℝ)..x, (Real.log t ^ n)⁻¹) <
      x / Real.log x ^ n +
        (n : ℝ) * (√x / Real.log 2 ^ (n + 1) + 2 ^ (n + 1) * x / Real.log x ^ (n + 1)) := by
  have h := integral_inv_log_rpow_lt_div_add (k := (n : ℝ)) (Nat.cast_pos.mpr hn) hx
  simpa only [Real.rpow_natCast, ← Nat.cast_add_one] using h

/-! ### Asymptotic expansion of `Li` and `li` -/

/-- Exact `n`-fold integration-by-parts expansion of `Li x` for every `n : ℕ` and `x > 1`. -/
theorem logIntegral_eq_sum_add_integral (n : ℕ) {x : ℝ} (hx : 1 < x) :
    logIntegral x =
      (x / Real.log x) * (∑ k ∈ Finset.range n, (k ! : ℝ) / Real.log x ^ k) -
        (2 / Real.log 2) * (∑ k ∈ Finset.range n, (k ! : ℝ) / Real.log 2 ^ k) +
        (n ! : ℝ) * ∫ t in (2 : ℝ)..x, (Real.log t ^ (n + 1))⁻¹ := by
  induction n with
  | zero =>
      simp [logIntegral_def]
  | succ n ih =>
      rw [ih, integral_inv_log_pow_eq_sub_add (n + 1) one_lt_two hx,
        Finset.sum_range_succ, Finset.sum_range_succ, mul_add, mul_add, mul_add,
        Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hterm (y : ℝ) : (y / Real.log y) * ((n ! : ℝ) / Real.log y ^ n) =
          (n ! : ℝ) * (y / Real.log y ^ (n + 1)) := by
        rw [pow_succ']
        ring
      rw [hterm x, hterm 2]
      ring

/-- The remainder integral `∫ t in 2..x, (log t ^ (n + 1))⁻¹` is `O(x / log x ^ (n + 1))`. -/
theorem isBigO_integral_inv_log_pow (n : ℕ) :
    (fun x : ℝ ↦ ∫ t in (2 : ℝ)..x, (Real.log t ^ (n + 1))⁻¹) =O[atTop]
      fun x : ℝ ↦ x / Real.log x ^ (n + 1) := by
  have ho : (fun x : ℝ ↦ Real.log x ^ (n + 1)) =o[atTop] fun x : ℝ ↦ √x := by
    refine (isLittleO_log_rpow_rpow_atTop (r := ((n + 1 : ℕ) : ℝ)) (s := 1 / 2)
      (by norm_num)).congr' ?_ ?_
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x _
      exact Real.rpow_natCast _ _
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x _
      exact (Real.sqrt_eq_rpow x).symm
  have hsqrt_le : ∀ᶠ x : ℝ in atTop,
      √x / Real.log 2 ^ (n + 1) ≤ x / Real.log x ^ (n + 1) := by
    have hlim : Tendsto (fun x : ℝ ↦ Real.log x ^ (n + 1) / √x) atTop (𝓝 0) :=
      ho.tendsto_div_nhds_zero
    filter_upwards [eventually_gt_atTop (2 : ℝ),
      hlim.eventually (Iio_mem_nhds (pow_pos (Real.log_pos one_lt_two) (n + 1)))]
      with x hx hratio
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    have hsqx : 0 < √x := Real.sqrt_pos.mpr (by linarith)
    have hmul : Real.log x ^ (n + 1) ≤ Real.log 2 ^ (n + 1) * √x :=
      (div_le_iff₀ hsqx).mp (le_of_lt hratio)
    rw [div_le_div_iff₀ (pow_pos (Real.log_pos one_lt_two) _) (pow_pos hlogx _)]
    calc √x * Real.log x ^ (n + 1)
        ≤ √x * (Real.log 2 ^ (n + 1) * √x) := mul_le_mul_of_nonneg_left hmul hsqx.le
      _ = (√x * √x) * Real.log 2 ^ (n + 1) := by ring
      _ = x * Real.log 2 ^ (n + 1) := by rw [Real.mul_self_sqrt (by linarith)]
  refine IsBigO.of_bound (1 + 2 ^ (n + 1)) ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ), hsqrt_le] with x hx hsq
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hnn : 0 ≤ ∫ t in (2 : ℝ)..x, (Real.log t ^ (n + 1))⁻¹ :=
    integral_inv_log_pow_nonneg (n + 1) one_lt_two hx
  rw [Real.norm_of_nonneg hnn, Real.norm_of_nonneg (by positivity)]
  calc ∫ t in (2 : ℝ)..x, (Real.log t ^ (n + 1))⁻¹
      ≤ √x / Real.log 2 ^ (n + 1) + 2 ^ (n + 1) * x / Real.log x ^ (n + 1) :=
        integral_inv_log_pow_le_sqrt_add (n + 1) hx
    _ ≤ x / Real.log x ^ (n + 1) + 2 ^ (n + 1) * x / Real.log x ^ (n + 1) := by gcongr
    _ = (1 + 2 ^ (n + 1)) * (x / Real.log x ^ (n + 1)) := by ring

/-- A constant is `o(x / log x ^ n)` as `x → ∞` for every `n : ℕ`. -/
theorem isLittleO_const_div_log_pow (c : ℝ) (n : ℕ) :
    (fun _ : ℝ ↦ c) =o[atTop] fun x : ℝ ↦ x / Real.log x ^ n := by
  have ho : (fun x : ℝ ↦ Real.log x ^ n) =o[atTop] fun x : ℝ ↦ x := by
    refine (isLittleO_log_rpow_rpow_atTop (r := (n : ℝ)) (s := 1) one_pos).congr' ?_ ?_
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x _
      exact Real.rpow_natCast _ _
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x _
      exact Real.rpow_one x
  have hpos : Tendsto (fun x : ℝ ↦ Real.log x ^ n / x) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ho.tendsto_div_nhds_zero <| by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact div_pos (pow_pos (Real.log_pos hx) n) (zero_lt_one.trans hx)
  have htop : Tendsto (fun x : ℝ ↦ x / Real.log x ^ n) atTop atTop :=
    hpos.inv_tendsto_nhdsGT_zero.congr fun x ↦ inv_div _ _
  exact isLittleO_const_left.mpr <| Or.inr <|
    (tendsto_abs_atTop_atTop.comp htop).congr fun _ ↦ (Real.norm_eq_abs _).symm

/-- **Asymptotic expansion of `Li`**: for every `n : ℕ`,
`Li x - (x / log x) * ∑ k ∈ range n, k! / log x ^ k = O(x / log x ^ (n + 1))`. -/
theorem logIntegral_sub_sum_isBigO (n : ℕ) :
    (fun x : ℝ ↦
      logIntegral x - (x / Real.log x) * ∑ k ∈ Finset.range n, (k ! : ℝ) / Real.log x ^ k)
      =O[atTop] fun x : ℝ ↦ x / Real.log x ^ (n + 1) := by
  have hconst := (isLittleO_const_div_log_pow
    (-(2 / Real.log 2) * ∑ k ∈ Finset.range n, (k ! : ℝ) / Real.log 2 ^ k) (n + 1)).isBigO
  have hrem := (isBigO_integral_inv_log_pow n).const_mul_left (n ! : ℝ)
  refine (hconst.add hrem).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [logIntegral_eq_sum_add_integral n hx]
  ring

/-- **Asymptotic expansion of `li`**: for every `n : ℕ`,
`li x - (x / log x) * ∑ k ∈ range n, k! / log x ^ k = O(x / log x ^ (n + 1))`. -/
theorem li_sub_sum_isBigO (n : ℕ) :
    (fun x : ℝ ↦
      li x - (x / Real.log x) * ∑ k ∈ Finset.range n, (k ! : ℝ) / Real.log x ^ k)
      =O[atTop] fun x : ℝ ↦ x / Real.log x ^ (n + 1) := by
  refine ((logIntegral_sub_sum_isBigO n).add
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
theorem li_isEquivalent_div_log : li ~[atTop] fun x : ℝ ↦ x / Real.log x :=
  li_isEquivalent_logIntegral.trans logIntegral_isEquivalent_div_log

/-! ### Numerical enclosures of `li 2` -/

/-- Partial-sum lower bound for the entire-part series `∑_{n ≥ 1} y^n / (n * n!)` when `y ≥ 0`. -/
theorem sum_range_le_tsum_pow_div_mul_factorial {y : ℝ} (hy : 0 ≤ y) (N : ℕ) :
    (∑ n ∈ Finset.range N, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) ≤
      ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) :=
  (summable_pow_div_mul_factorial y).sum_le_tsum (Finset.range N) fun _ _ ↦ by positivity

/-- Geometric-tail upper bound for the entire-part series `∑_{n ≥ 1} y^n / (n * n!)` when
`0 ≤ y < N + 2`. -/
theorem tsum_pow_div_mul_factorial_le_sum_range_add {y : ℝ} (hy : 0 ≤ y) {N : ℕ}
    (hN : y < (N : ℝ) + 2) :
    (∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) ≤
      (∑ n ∈ Finset.range N, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) +
        (y ^ (N + 1) / (((N : ℝ) + 1) * ((N + 1)! : ℝ))) / (1 - y / ((N : ℝ) + 2)) := by
  let a : ℕ → ℝ := fun n ↦ y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))
  let r : ℝ := y / ((N : ℝ) + 2)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := (div_lt_one (by positivity)).mpr hN
  have hsum := summable_pow_div_mul_factorial y
  rw [← hsum.sum_add_tsum_nat_add N]
  gcongr
  have hterm : ∀ k : ℕ, a (k + N) ≤ a N * r ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hstep : a (k + 1 + N) ≤ a (k + N) * r := by
          dsimp only [a, r]
          rw [add_right_comm k 1 N, pow_succ, Nat.factorial_succ, Nat.cast_mul]
          rw [← mul_div_mul_comm, div_le_div_iff₀ (by positivity) (by positivity)]
          have hcast1 : ((k + N + 1 : ℕ) : ℝ) + 1 = (N : ℝ) + k + 2 := by push_cast; ring
          have hcast2 : ((k + N : ℕ) : ℝ) + 1 = (N : ℝ) + k + 1 := by push_cast; ring
          have hcast3 : ((k + N + 1 + 1 : ℕ) : ℝ) = (N : ℝ) + k + 2 := by push_cast; ring
          rw [hcast1, hcast2, hcast3]
          have hmul_le : ((N : ℝ) + k + 1) * ((N : ℝ) + 2) ≤
              ((N : ℝ) + k + 2) * ((N : ℝ) + k + 2) := by
            nlinarith [Nat.cast_nonneg (α := ℝ) k, Nat.cast_nonneg (α := ℝ) N]
          have hyk : 0 ≤ y ^ (k + N + 1) * y * ((k + N + 1)! : ℝ) := by positivity
          nlinarith
        calc a (k + 1 + N)
            ≤ a (k + N) * r := hstep
          _ ≤ (a N * r ^ k) * r := mul_le_mul_of_nonneg_right ih hr0
          _ = a N * r ^ (k + 1) := by rw [pow_succ, mul_assoc]
  have hgeom : Summable fun k : ℕ ↦ a N * r ^ k :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left (a N)
  calc (∑' k : ℕ, a (k + N))
      ≤ ∑' k : ℕ, a N * r ^ k := ((summable_nat_add_iff N).mpr hsum).tsum_le_tsum hterm hgeom
    _ = a N / (1 - r) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]

/-- Monotonicity of the entire-part series `∑_{n ≥ 1} y^n / (n * n!)` on `[0, ∞)`. -/
theorem tsum_pow_div_mul_factorial_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    (∑' n : ℕ, x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) ≤
      ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) :=
  (summable_pow_div_mul_factorial x).tsum_le_tsum
    (fun n ↦ div_le_div_of_nonneg_right (pow_le_pow_left₀ hx hxy _) (by positivity))
    (summable_pow_div_mul_factorial y)

/-- Lower bound `0.8344605 ≤ ∑_{n ≥ 1} (log 2)^n / (n * n!)`. -/
theorem le_tsum_log_two_pow_div_mul_factorial :
    (0.8344605 : ℝ) ≤
      ∑' n : ℕ, Real.log 2 ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
  have hlog : (0.693147 : ℝ) ≤ Real.log 2 := le_trans (by norm_num) Real.log_two_gt_d9.le
  refine le_trans ?_ (tsum_pow_div_mul_factorial_mono (by norm_num) hlog)
  refine le_trans ?_ (sum_range_le_tsum_pow_div_mul_factorial (y := (0.693147 : ℝ)) (by norm_num) 7)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]
  norm_num

/-- Upper bound `∑_{n ≥ 1} (log 2)^n / (n * n!) ≤ 0.8344615`. -/
theorem tsum_log_two_pow_div_mul_factorial_le :
    (∑' n : ℕ, Real.log 2 ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) ≤ 0.8344615 := by
  have hlog : Real.log 2 ≤ 0.6931472 := le_trans Real.log_two_lt_d9.le (by norm_num)
  refine (tsum_pow_div_mul_factorial_mono (Real.log_pos one_lt_two).le hlog).trans ?_
  refine (tsum_pow_div_mul_factorial_le_sum_range_add (y := (0.6931472 : ℝ))
    (by norm_num) (N := 7) (by norm_num)).trans ?_
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]
  norm_num

/-- Lower bound `-0.366513 ≤ log (log 2)`. -/
theorem le_log_log_two : (-0.366513 : ℝ) ≤ Real.log (Real.log 2) := by
  rw [Real.le_log_iff_exp_le (Real.log_pos one_lt_two)]
  have he := Real.sum_le_exp_of_nonneg (x := (366513 / 1000000 : ℝ)) (by norm_num) 8
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at he
  norm_num at he
  have hmul : Real.exp (-(366513 / 1000000 : ℝ)) * Real.exp (366513 / 1000000) = 1 := by
    rw [← Real.exp_add]; norm_num
  have hlt : Real.exp (-(366513 / 1000000 : ℝ)) ≤ 6931471803 / 10000000000 := by nlinarith
  have hlt' : Real.exp (-0.366513) ≤ 0.6931471803 := by norm_num at hlt ⊢; exact hlt
  exact hlt'.trans Real.log_two_gt_d9.le

/-- Upper bound `log (log 2) ≤ -0.366512`. -/
theorem log_log_two_le : Real.log (Real.log 2) ≤ -0.366512 := by
  rw [Real.log_le_iff_le_exp (Real.log_pos one_lt_two)]
  have hb := Real.exp_bound' (x := (22907 / 62500 : ℝ)) (by norm_num) (by norm_num)
    (n := 8) (by decide)
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at hb
  norm_num at hb
  have hmul : Real.exp (-(22907 / 62500 : ℝ)) * Real.exp (22907 / 62500) = 1 := by
    rw [← Real.exp_add]; norm_num
  have hle : (6931471808 / 10000000000 : ℝ) ≤ Real.exp (-(22907 / 62500 : ℝ)) := by
    nlinarith [Real.exp_pos (-(22907 / 62500 : ℝ)), Real.exp_pos (22907 / 62500 : ℝ)]
  have hle' : (0.6931471808 : ℝ) ≤ Real.exp (-0.366512) := by norm_num at hle ⊢; exact hle
  exact Real.log_two_lt_d9.le.trans hle'

/-- Unconditional lower bound `0.96 < li 2` using Mathlib's `1 / 2 < γ`. -/
theorem lt_li_two : (0.96 : ℝ) < li 2 := by
  rw [li_def]
  linarith [Real.one_half_lt_eulerMascheroniConstant, le_log_log_two,
    le_tsum_log_two_pow_div_mul_factorial]

/-- Unconditional upper bound `li 2 < 1.14` using Mathlib's `γ < 2 / 3`. -/
theorem li_two_lt : li 2 < 1.14 := by
  rw [li_def]
  linarith [Real.eulerMascheroniConstant_lt_two_thirds, log_log_two_le,
    tsum_log_two_pow_div_mul_factorial_le]

/-- Conditional lower bound `1.0451 ≤ li 2` given `|γ - 0.5772156649| < 10⁻⁹`. -/
theorem le_li_two_of_abs_eulerMascheroniConstant_sub_lt
    (hγ : |Real.eulerMascheroniConstant - 0.5772156649| < 10 ^ (-(9 : ℤ))) :
    (1.0451 : ℝ) ≤ li 2 := by
  rw [abs_lt] at hγ
  norm_num at hγ
  rw [li_def]
  linarith [hγ.1, le_log_log_two, le_tsum_log_two_pow_div_mul_factorial]

/-- Conditional upper bound `li 2 ≤ 1.0452` given `|γ - 0.5772156649| < 10⁻⁹`. -/
theorem li_two_le_of_abs_eulerMascheroniConstant_sub_lt
    (hγ : |Real.eulerMascheroniConstant - 0.5772156649| < 10 ^ (-(9 : ℤ))) :
    li 2 ≤ 1.0452 := by
  rw [abs_lt] at hγ
  norm_num at hγ
  rw [li_def]
  linarith [hγ.2, log_log_two_le, tsum_log_two_pow_div_mul_factorial_le]

/-! ### Bounds and unique zero of `Li x - x / log x` -/

/-- The derivative of `x ↦ Li x - x / log x` on `(1, ∞)` is `(log x ^ 2)⁻¹`. -/
theorem hasDerivAt_logIntegral_sub_div_log {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun t : ℝ ↦ logIntegral t - t / Real.log t) (Real.log x ^ 2)⁻¹ x := by
  have hd := (hasDerivAt_logIntegral hx).fun_sub (hasDerivAt_div_log_pow 1 (Real.log_pos hx).ne')
  simpa only [pow_one, Nat.cast_one, one_mul, sub_sub_cancel] using hd

/-- `x ↦ Li x - x / log x` is strictly increasing on `(1, ∞)`. -/
theorem strictMonoOn_logIntegral_sub_div_log :
    StrictMonoOn (fun x : ℝ ↦ logIntegral x - x / Real.log x) (Ioi 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 1)
    (fun x hx ↦ (hasDerivAt_logIntegral_sub_div_log hx).continuousAt.continuousWithinAt)
    fun x hx ↦ ?_
  rw [interior_Ioi] at hx
  rw [(hasDerivAt_logIntegral_sub_div_log hx).deriv]
  exact inv_pos.mpr (pow_pos (Real.log_pos hx) 2)

/-- Lower bound `x / log x ^ 2 - 2 / log 2 - 2 / log 2 ^ 2 ≤ Li x - x / log x` for `x ≥ 2`. -/
theorem le_logIntegral_sub_div_log {x : ℝ} (hx : 2 ≤ x) :
    x / Real.log x ^ 2 - 2 / Real.log 2 - 2 / Real.log 2 ^ 2 ≤
      logIntegral x - x / Real.log x := by
  rw [logIntegral_eq_div_log_sub_add hx,
    integral_inv_log_pow_eq_sub_add 2 one_lt_two (by linarith)]
  have hnn := integral_inv_log_pow_nonneg 3 one_lt_two hx
  norm_num
  linarith

/-- Strict lower bound `x / log x ^ 2 - 2 / log 2 - 2 / log 2 ^ 2 < Li x - x / log x` for
`x > 2`. -/
theorem lt_logIntegral_sub_div_log {x : ℝ} (hx : 2 < x) :
    x / Real.log x ^ 2 - 2 / Real.log 2 - 2 / Real.log 2 ^ 2 <
      logIntegral x - x / Real.log x := by
  rw [logIntegral_eq_div_log_sub_add hx.le,
    integral_inv_log_pow_eq_sub_add 2 one_lt_two (by linarith)]
  have hpos : 0 < ∫ t in (2 : ℝ)..x, (Real.log t ^ 3)⁻¹ :=
    lt_of_lt_of_le (div_pos (by linarith) (pow_pos (Real.log_pos (by linarith)) 3))
      (le_integral_inv_log_pow 3 one_lt_two hx.le)
  norm_num
  linarith

/-- Strict upper bound for `Li x - x / log x` on `[2, ∞)`. -/
theorem logIntegral_sub_div_log_lt {x : ℝ} (hx : 2 ≤ x) :
    logIntegral x - x / Real.log x <
      x / Real.log x ^ 2 + 2 * √x / Real.log 2 ^ 3 + 16 * x / Real.log x ^ 3 -
        2 / Real.log 2 := by
  rw [logIntegral_eq_div_log_sub_add hx]
  have hb := integral_inv_log_pow_lt_div_add (n := 2) (by decide) hx
  norm_num at hb ⊢
  have hdist : 2 * (√x / Real.log 2 ^ 3 + 8 * x / Real.log x ^ 3) =
      2 * √x / Real.log 2 ^ 3 + 16 * x / Real.log x ^ 3 := by ring
  linarith

/-- Series representation of `Li x` eliminating the Euler–Mascheroni constant `γ`:
`Li x = log (log x / log 2) + ∑_{n ≥ 1} ((log x)^n - (log 2)^n) / (n * n!)` for `x > 1`. -/
theorem logIntegral_eq_log_div_add_tsum_sub {x : ℝ} (hx : 1 < x) :
    logIntegral x = Real.log (Real.log x / Real.log 2) +
      (∑' n : ℕ, Real.log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) -
      ∑' n : ℕ, Real.log 2 ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
  rw [logIntegral_eq_li_sub_li_two hx, li_def, li_def,
    Real.log_div (Real.log_pos hx).ne' (Real.log_pos one_lt_two).ne']
  ring

private theorem log_div_log_two_eq_one_add {x : ℝ} (hx : 1 < x) :
    Real.log (Real.log x / Real.log 2) =
      1 + Real.log (Real.log x / (Real.exp 1 * Real.log 2)) := by
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hfac : Real.log x / Real.log 2 = Real.exp 1 * (Real.log x / (Real.exp 1 * Real.log 2)) := by
    field_simp [(Real.exp_pos 1).ne', (Real.log_pos one_lt_two).ne']
  rw [hfac, Real.log_mul (Real.exp_pos 1).ne'
    (div_pos hlogx (mul_pos (Real.exp_pos 1) (Real.log_pos one_lt_two))).ne', Real.log_exp]

private theorem logIntegral_sub_div_log_neg_at :
    logIntegral 6.5797 - 6.5797 / Real.log 6.5797 < 0 := by
  -- Step 1: Upper bound `log 6.5797 ≤ 1.8839895` via `log 6.5797 = 3 log 2 + log (1 - u)`.
  have hlogx : Real.log 6.5797 ≤ 1.8839895 := by
    have hsplit : Real.log 6.5797 = 3 * Real.log 2 + Real.log (1 - 14203 / 80000) := by
      have hprod : (6.5797 : ℝ) = 2 ^ 3 * (1 - 14203 / 80000) := by norm_num
      rw [hprod, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
      norm_num
    have ht := Real.abs_log_sub_add_sum_range_le (x := (14203 / 80000 : ℝ)) (by norm_num) 8
    rw [abs_le] at ht
    have hupper := ht.2
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at hupper
    norm_num at hupper
    linarith [Real.log_two_lt_d9]
  have hlogx_pos : 0 < Real.log 6.5797 := Real.log_pos (by norm_num)
  -- Step 2: Upper bound `log (log 6.5797 / log 2) ≤ log 6.5797 / (e * log 2)`.
  have hloglog : Real.log (Real.log 6.5797 / Real.log 2) ≤
      1.8839895 / (2.7182818283 * 0.6931471803) := by
    have hr : Real.log 6.5797 / (Real.exp 1 * Real.log 2) ≤
        1.8839895 / (2.7182818283 * 0.6931471803) :=
      div_le_div₀ (by norm_num) hlogx (by norm_num)
        (mul_le_mul Real.exp_one_gt_d9.le Real.log_two_gt_d9.le (by norm_num) (Real.exp_pos 1).le)
    have h1 := log_div_log_two_eq_one_add (x := 6.5797) (by norm_num)
    have h2 := Real.log_le_sub_one_of_pos
      (div_pos hlogx_pos (mul_pos (Real.exp_pos 1) (Real.log_pos one_lt_two)))
    linarith
  -- Step 3: Upper bound the series at `log 6.5797 ≤ 1.8839895` with 8 terms + geometric tail.
  have hser : (∑' n : ℕ, Real.log 6.5797 ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) ≤
      3.326983 := by
    refine (tsum_pow_div_mul_factorial_mono hlogx_pos.le hlogx).trans ?_
    refine (tsum_pow_div_mul_factorial_le_sum_range_add (y := (1.8839895 : ℝ))
      (by norm_num) (N := 8) (by norm_num)).trans ?_
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]
    norm_num
  -- Step 4: Lower bound `6.5797 / log 6.5797 ≥ 6.5797 / 1.8839895` and combine.
  have hdiv : (6.5797 : ℝ) / 1.8839895 ≤ 6.5797 / Real.log 6.5797 :=
    div_le_div_of_nonneg_left (by norm_num) hlogx_pos hlogx
  rw [logIntegral_eq_log_div_add_tsum_sub (by norm_num)]
  linarith [le_tsum_log_two_pow_div_mul_factorial]

private theorem logIntegral_sub_div_log_pos_at :
    0 < logIntegral 6.5798 - 6.5798 / Real.log 6.5798 := by
  -- Step 1: Lower bound `1.884004 ≤ log 6.5798` via `log 6.5798 = 3 log 2 + log (1 - u)`.
  have hlogx : (1.884004 : ℝ) ≤ Real.log 6.5798 := by
    have hsplit : Real.log 6.5798 = 3 * Real.log 2 + Real.log (1 - 7101 / 40000) := by
      have hprod : (6.5798 : ℝ) = 2 ^ 3 * (1 - 7101 / 40000) := by norm_num
      rw [hprod, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
      norm_num
    have ht := Real.abs_log_sub_add_sum_range_le (x := (7101 / 40000 : ℝ)) (by norm_num) 8
    rw [abs_le] at ht
    have hlower := ht.1
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at hlower
    norm_num at hlower
    linarith [Real.log_two_gt_d9]
  have hlogx_pos : 0 < Real.log 6.5798 := by linarith
  -- Step 2: Lower bound `log (log 6.5798 / log 2) ≥ 2 - (e * log 2) / log 6.5798`.
  have hloglog : 2 - (2.7182818286 * 0.6931471808) / 1.884004 ≤
      Real.log (Real.log 6.5798 / Real.log 2) := by
    have hinv : (Real.exp 1 * Real.log 2) / Real.log 6.5798 ≤
        (2.7182818286 * 0.6931471808) / 1.884004 :=
      div_le_div₀ (by norm_num)
        (mul_le_mul Real.exp_one_lt_d9.le Real.log_two_lt_d9.le (Real.log_pos one_lt_two).le
          (by norm_num))
        (by norm_num) hlogx
    have h1 := log_div_log_two_eq_one_add (x := 6.5798) (by norm_num)
    have h2 := Real.one_sub_inv_le_log_of_pos
      (div_pos hlogx_pos (mul_pos (Real.exp_pos 1) (Real.log_pos one_lt_two)))
    rw [inv_div] at h2
    linarith
  -- Step 3: Lower bound the series at `log 6.5798 ≥ 1.884004` with 10 terms.
  have hser : (3.327019 : ℝ) ≤
      ∑' n : ℕ, Real.log 6.5798 ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
    refine le_trans ?_ (tsum_pow_div_mul_factorial_mono (by norm_num) hlogx)
    refine le_trans ?_ (sum_range_le_tsum_pow_div_mul_factorial (y := (1.884004 : ℝ))
      (by norm_num) 10)
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]
    norm_num
  -- Step 4: Upper bound `6.5798 / log 6.5798 ≤ 6.5798 / 1.884004` and combine.
  have hdiv : 6.5798 / Real.log 6.5798 ≤ 6.5798 / 1.884004 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlogx
  rw [logIntegral_eq_log_div_add_tsum_sub (by norm_num)]
  linarith [tsum_log_two_pow_div_mul_factorial_le]

/-- `Li x - x / log x < 0` for every `1 < x ≤ 6.5797`. -/
theorem logIntegral_sub_div_log_neg {x : ℝ} (hx1 : 1 < x) (hx : x ≤ 6.5797) :
    logIntegral x - x / Real.log x < 0 := by
  rcases eq_or_lt_of_le hx with rfl | hlt
  · exact logIntegral_sub_div_log_neg_at
  · exact (strictMonoOn_logIntegral_sub_div_log hx1 (by norm_num) hlt).trans
      logIntegral_sub_div_log_neg_at

/-- `0 < Li x - x / log x` for every `x ≥ 6.5798`. -/
theorem logIntegral_sub_div_log_pos {x : ℝ} (hx : 6.5798 ≤ x) :
    0 < logIntegral x - x / Real.log x := by
  rcases eq_or_lt_of_le hx with rfl | hlt
  · exact logIntegral_sub_div_log_pos_at
  · exact logIntegral_sub_div_log_pos_at.trans
      (strictMonoOn_logIntegral_sub_div_log (by norm_num) (mem_Ioi.mpr (by linarith)) hlt)

/-- `Li x - x / log x` has a unique zero in `(6.5797, 6.5798)`. -/
theorem existsUnique_logIntegral_eq_div_log_Ioo :
    ∃! x ∈ Ioo (6.5797 : ℝ) 6.5798, logIntegral x - x / Real.log x = 0 := by
  have hcont : ContinuousOn (fun t : ℝ ↦ logIntegral t - t / Real.log t) (Icc 6.5797 6.5798) :=
    fun t ht ↦
      (hasDerivAt_logIntegral_sub_div_log (by linarith [ht.1])).continuousAt.continuousWithinAt
  have h0 : (0 : ℝ) ∈ Icc (logIntegral 6.5797 - 6.5797 / Real.log 6.5797)
      (logIntegral 6.5798 - 6.5798 / Real.log 6.5798) :=
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
theorem existsUnique_logIntegral_eq_div_log :
    ∃! x ∈ Ioi (1 : ℝ), logIntegral x - x / Real.log x = 0 := by
  obtain ⟨x₀, ⟨⟨hx₀_lo, _⟩, hfx₀⟩, _⟩ := existsUnique_logIntegral_eq_div_log_Ioo
  refine ⟨x₀, ⟨mem_Ioi.mpr (by linarith), hfx₀⟩, fun y ⟨hy, hfy⟩ ↦ ?_⟩
  exact strictMonoOn_logIntegral_sub_div_log.injOn hy (mem_Ioi.mpr (by linarith))
    (hfy.trans hfx₀.symm)

/-- **Fiori–Kadiri–Swidinsky (2023), Lemma 20**: for every `x ≥ 6.58`,
`(x - 6.58) / log x ^ 2 ≤ Li x - x / log x`. -/
theorem div_log_sq_le_logIntegral_sub_div_log {x : ℝ} (hx : 6.58 ≤ x) :
    (x - 6.58) / Real.log x ^ 2 ≤ logIntegral x - x / Real.log x := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (6.58 : ℝ)) (b := x)
    (f := fun t : ℝ ↦ logIntegral t - t / Real.log t)
    (f' := fun t : ℝ ↦ (Real.log t ^ 2)⁻¹)
    (fun t ht ↦ by
      rw [uIcc_of_le hx] at ht
      exact hasDerivAt_logIntegral_sub_div_log (by linarith [ht.1]))
    (intervalIntegrable_inv_log_pow 2 (by norm_num) (by linarith))
  have hpos : 0 < logIntegral 6.58 - 6.58 / Real.log 6.58 :=
    logIntegral_sub_div_log_pos (by norm_num)
  have hlow := le_integral_inv_log_pow 2 (by norm_num : (1 : ℝ) < 6.58) hx
  linarith

end TauCeti.Real
