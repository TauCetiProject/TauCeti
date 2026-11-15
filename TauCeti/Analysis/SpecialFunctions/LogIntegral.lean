/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.InvLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import TauCeti.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Asymptotics.Lemmas

/-!
# The logarithmic integral

This file defines the offset logarithmic integral `Li x = ∫ t in 2..x, (log t)⁻¹` and proves the
prime-number-theorem normalisation `Li x ~ x / log x` as `x → ∞`.

The lower endpoint is `2` rather than `0`: the integrand has a nonintegrable singularity at
`t = 1`, so the unshifted `li` exists only as a principal value, while every arithmetic
application compares a prime count with `Li`. The endpoint agrees with the one used by the
partial-summation identities for prime counts, so the two can be combined without a shift of
origin.

The asymptotic is proved from the exact identity
`Li x = x / log x - 2 / log 2 + ∫ t in 2..x, ((log t) ^ 2)⁻¹`,
the fundamental theorem of calculus applied to `t ↦ t / log t`, together with the estimate that
the remaining integral is `o (x / log x)`. Splitting that integral at `√x` bounds it by
`√x / (log 2) ^ 2 + 4 * x / (log x) ^ 2`, and both terms are `o (x / log x)`.

## Main declarations

* `TauCeti.Real.logIntegral` — the offset logarithmic integral.
* `TauCeti.Real.logIntegral_of_le_one` — `Li x = 0` at and below the singularity `x = 1`.
* `TauCeti.Real.hasDerivAt_logIntegral` — its derivative `(log x)⁻¹` for `x > 1`.
* `TauCeti.Real.le_logIntegral` — the elementary lower bound `(x - 2) / log x ≤ Li x`.
* `TauCeti.Real.integral_rpow_sub_one_div_log` — the power substitution
  `∫ t in a..b, t ^ (β - 1) / log t = Li (b ^ β) - Li (a ^ β)` for `β > 0`.
* `TauCeti.Real.rpow_div_mul_log_add_integral_eq_logIntegral_rpow` — the Abel-summation identity
  turning `x ^ β / β` into `Li (x ^ β) - Li (2 ^ β)` up to the base-point boundary term.
* `TauCeti.Real.integral_inv_log_pow_eq_sub_add` — integration by parts for every reciprocal
  logarithm power, with either orientation of the interval.
* `TauCeti.Real.logIntegral_eq_div_log_sub_add` — the antiderivative identity above.
* `TauCeti.Real.logIntegral_isEquivalent_div_log` — `Li x ~ x / log x` at infinity, with the
  quotient form `TauCeti.Real.tendsto_logIntegral_mul_log_div_atTop`.
* `TauCeti.Real.tendsto_div_div_log_of_isLittleO_logIntegral` — an `o (x / log x)` error
  relative to `δ Li x` gives `f x / (x / log x) → δ`.
* `TauCeti.Real.isLittleO_integral_div_mul_log_sq` — for `f` interval integrable above `2` and of
  at most linear growth, `∫ t in 2..x, f t / (t * log t ^ 2)` is `o (x / log x)`.
* `TauCeti.Real.isLittleO_integral_div_mul_log_sq_of_isBigO_exp_neg_mul_sqrt_log` — for
  `f = O(x exp (-c √log x))`, the same weighted remainder integral is `o(x exp (-c √log x))` with
  no loss in `c`, and `TauCeti.Real.isLittleO_logIntegral_rpow_mul_exp_neg_mul_sqrt_log` absorbs
  `Li (x ^ β)` for `β < 1`.

The auxiliary bounds `TauCeti.Real.integral_inv_log_pow_le` and
`TauCeti.Real.le_integral_inv_log_pow` estimate `∫ t in a..b, ((log t) ^ n)⁻¹` by monotonicity of
the logarithm. They are stated for a general exponent because the identity above needs `n = 2`
while `Li` itself is the case `n = 1`.

## Use in prime counting

These are the analytic inputs to the transfer `ϑ(x) ∼ δx ⟹ π(x) ∼ δ Li(x)`,
`TauCeti.primeCount_asymptotic_of_primeTheta`, and to its effective companion with power secondary
terms and `O(x exp (-c √log x))` remainder in
`TauCeti/NumberTheory/ArithmeticDirichletSeries/Transfer.lean`. The weighted-remainder estimates
`TauCeti.Real.isLittleO_integral_div_mul_log_sq` and
`TauCeti.Real.isLittleO_integral_div_mul_log_sq_of_isBigO_exp_neg_mul_sqrt_log` absorb the
integral produced by Abel summation there.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 1.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.

The integration-by-parts recurrence is adapted
from the Ramanujan estimates in the [PrimeNumberTheoremAnd project](https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/dc6e36e/PrimeNumberTheoremAnd/IEANTN/Ramanujan/Ramanujan.lean).

Mathlib's `Mathlib/NumberTheory/Chebyshev.lean` carries out this estimate for the rational
Chebyshev function, in `Chebyshev.integral_theta_div_log_sq_isLittleO`; the argument for a general
integrand below follows the same split into a bounded initial segment and a linearly bounded tail.
-/

public section

namespace TauCeti.Real

open Asymptotics Filter MeasureTheory Set
open scoped Topology

/-! ### Reciprocal powers of the logarithm -/

/-- Reciprocal powers of the logarithm are continuous to the right of its zero `t = 1`. -/
theorem continuousOn_inv_log_pow (n : ℕ) :
    ContinuousOn (fun t : ℝ ↦ (Real.log t ^ n)⁻¹) (Ioi 1) := by
  have hlog : ContinuousOn (fun t : ℝ ↦ Real.log t) (Ioi 1) :=
    Real.continuousOn_log.mono fun t ht ↦ ne_of_gt (lt_trans one_pos ht)
  exact (hlog.pow n).inv₀ fun t ht ↦ ne_of_gt (pow_pos (Real.log_pos ht) n)

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
  refine ((continuousOn_inv_log_pow n).mono fun t ht ↦ ?_).intervalIntegrable
  rw [mem_uIcc] at ht
  rcases ht with ht | ht
  · exact lt_of_lt_of_le ha ht.1
  · exact lt_of_lt_of_le hb ht.1

/-- Monotonicity of the logarithm bounds `∫ t in a..b, (log t ^ n)⁻¹` above by the value of the
integrand at the left endpoint. -/
theorem integral_inv_log_pow_le (n : ℕ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, (Real.log t ^ n)⁻¹ ≤ (b - a) / Real.log a ^ n := by
  have hla : 0 < Real.log a := Real.log_pos ha
  have hb : 1 < b := lt_of_lt_of_le ha hab
  have hmono := intervalIntegral.integral_mono_on hab (intervalIntegrable_inv_log_pow n ha hb)
    (g := fun _ ↦ (Real.log a ^ n)⁻¹) intervalIntegrable_const (fun t ht ↦ ?_)
  · simpa [smul_eq_mul, div_eq_mul_inv] using hmono
  · exact inv_anti₀ (pow_pos hla n)
      (pow_le_pow_left₀ hla.le (Real.log_le_log (by linarith) ht.1) n)

/-- Monotonicity of the logarithm bounds `∫ t in a..b, (log t ^ n)⁻¹` below by the value of the
integrand at the right endpoint. -/
theorem le_integral_inv_log_pow (n : ℕ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (b - a) / Real.log b ^ n ≤ ∫ t in a..b, (Real.log t ^ n)⁻¹ := by
  have hla : 0 < Real.log a := Real.log_pos ha
  have hb : 1 < b := lt_of_lt_of_le ha hab
  have hmono := intervalIntegral.integral_mono_on hab
    (f := fun _ ↦ (Real.log b ^ n)⁻¹) intervalIntegrable_const
    (intervalIntegrable_inv_log_pow n ha hb) (fun t ht ↦ ?_)
  · simpa [smul_eq_mul, div_eq_mul_inv] using hmono
  · have hat : a ≤ t := ht.1
    have htb : t ≤ b := ht.2
    have hlt : 0 < Real.log t := lt_of_lt_of_le hla (Real.log_le_log (by linarith) hat)
    exact inv_anti₀ (pow_pos hlt n)
      (pow_le_pow_left₀ hlt.le (Real.log_le_log (by linarith) htb) n)

/-- The integrand `(log t ^ n)⁻¹` is nonnegative to the right of `1`, so its integral is. -/
theorem integral_inv_log_pow_nonneg (n : ℕ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    0 ≤ ∫ t in a..b, (Real.log t ^ n)⁻¹ := by
  refine intervalIntegral.integral_nonneg hab fun t ht ↦ ?_
  have : 0 < Real.log t := Real.log_pos (lt_of_lt_of_le ha ht.1)
  positivity

/-! ### The logarithmic integral -/

/-- The **offset logarithmic integral** `Li x = ∫ t in 2..x, (log t)⁻¹`.

The lower endpoint `2` avoids the singularity of the integrand at `t = 1`; this is the function
appearing in the prime number theorem in the form `π x ~ Li x`. -/
noncomputable def logIntegral (x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹

/-- Defining equation of `TauCeti.Real.logIntegral`. -/
theorem logIntegral_def (x : ℝ) : logIntegral x = ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹ := (rfl)

@[simp]
theorem logIntegral_two : logIntegral 2 = 0 := by
  rw [logIntegral_def, intervalIntegral.integral_same]

/-- The offset logarithmic integral has derivative `(log x)⁻¹` to the right of `1`. -/
theorem hasDerivAt_logIntegral {x : ℝ} (hx : 1 < x) :
    HasDerivAt logIntegral (Real.log x)⁻¹ x := by
  have hint : IntervalIntegrable (fun t : ℝ ↦ (Real.log t)⁻¹) volume 2 x := by
    simpa only [pow_one] using intervalIntegrable_inv_log_pow 1 one_lt_two hx
  simpa only [logIntegral] using! intervalIntegral.integral_hasDerivAt_right hint
    Real.measurable_log.inv.stronglyMeasurable.stronglyMeasurableAtFilter
    ((Real.continuousAt_log (zero_lt_one.trans hx).ne').inv₀ (Real.log_pos hx).ne')

/-- The offset logarithmic integral is differentiable on `(1, ∞)`. -/
theorem differentiableOn_logIntegral : DifferentiableOn ℝ logIntegral (Ioi 1) :=
  fun _ hx ↦ (hasDerivAt_logIntegral hx).differentiableAt.differentiableWithinAt

/-- The logarithmic integral is nonnegative from its base point on. -/
theorem logIntegral_nonneg {x : ℝ} (hx : 2 ≤ x) : 0 ≤ logIntegral x := by
  rw [logIntegral_def]
  simpa using integral_inv_log_pow_nonneg 1 one_lt_two hx

/-- The elementary lower bound `(x - 2) / log x ≤ Li x`, by monotonicity of the logarithm. -/
theorem le_logIntegral {x : ℝ} (hx : 2 ≤ x) : (x - 2) / Real.log x ≤ logIntegral x := by
  rw [logIntegral_def]
  simpa using le_integral_inv_log_pow 1 one_lt_two hx

/-! ### The asymptotic `Li x ~ x / log x` -/

/-- Integration by parts for reciprocal powers of the logarithm. Both endpoints lie to the
right of `1`; the signed interval integral allows either order of the endpoints. -/
theorem integral_inv_log_pow_eq_sub_add (n : ℕ) {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    (∫ t in a..b, (Real.log t ^ n)⁻¹) = b / Real.log b ^ n - a / Real.log a ^ n +
      (n : ℝ) * ∫ t in a..b, (Real.log t ^ (n + 1))⁻¹ := by
  have hi := intervalIntegrable_inv_log_pow n ha hb
  have hi1 := intervalIntegrable_inv_log_pow (n + 1) ha hb
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hasDerivAt_div_log_pow n (Real.log_pos (by
      rcases mem_uIcc.mp ht with ht | ht
      · exact ha.trans_le ht.1
      · exact hb.trans_le ht.1)).ne') (hi.sub (hi1.const_mul n))
  rw [intervalIntegral.integral_sub hi (hi1.const_mul n),
    intervalIntegral.integral_const_mul] at hFTC
  exact sub_eq_iff_eq_add.mp hFTC

/-- **The antiderivative identity for the logarithmic integral.** Integrating the derivative of
`t ↦ t / log t` from `2` to `x` writes `Li x` as `x / log x` plus a constant and a remainder
integral, which the asymptotic below shows is `o (x / log x)`. -/
theorem logIntegral_eq_div_log_sub_add {x : ℝ} (hx : 2 ≤ x) :
    logIntegral x =
      x / Real.log x - 2 / Real.log 2 + ∫ t in (2 : ℝ)..x, (Real.log t ^ 2)⁻¹ := by
  simpa only [logIntegral, pow_one, Nat.cast_one, one_mul] using
    integral_inv_log_pow_eq_sub_add 1 one_lt_two (one_lt_two.trans_le hx)

/-- Splitting at `√x` bounds the remainder integral of the antiderivative identity. -/
private theorem integral_inv_log_sq_le {x : ℝ} (hx : 4 ≤ x) :
    (∫ t in (2 : ℝ)..x, (Real.log t ^ 2)⁻¹) ≤ √x / Real.log 2 ^ 2 + 4 * x / Real.log x ^ 2 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hsq : 2 ≤ √x := by
    have h4 : √(4 : ℝ) ≤ √x := Real.sqrt_le_sqrt hx
    rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)] at h4
  have hle : √x ≤ x := by
    rw [Real.sqrt_le_self_iff]
    exact Or.inr (by linarith)
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogsq : Real.log √x = Real.log x / 2 := Real.log_sqrt hx0.le
  have hsplit : (∫ t in (2 : ℝ)..x, (Real.log t ^ 2)⁻¹) =
      (∫ t in (2 : ℝ)..√x, (Real.log t ^ 2)⁻¹) + ∫ t in √x..x, (Real.log t ^ 2)⁻¹ :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_inv_log_pow 2 one_lt_two (by linarith))
      (intervalIntegrable_inv_log_pow 2 (by linarith) (by linarith))).symm
  have hb₁ : (∫ t in (2 : ℝ)..√x, (Real.log t ^ 2)⁻¹) ≤ √x / Real.log 2 ^ 2 := by
    refine le_trans (integral_inv_log_pow_le 2 one_lt_two hsq) ?_
    gcongr
    linarith
  have hb₂ : (∫ t in √x..x, (Real.log t ^ 2)⁻¹) ≤ 4 * x / Real.log x ^ 2 := by
    refine le_trans (integral_inv_log_pow_le 2 (by linarith) hle) ?_
    rw [hlogsq, div_pow, div_div_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
    nlinarith [Real.sqrt_nonneg x]
  rw [hsplit]
  linarith

/-- The remainder integral of the antiderivative identity is `o (x / log x)`. -/
theorem tendsto_integral_inv_log_sq_mul_log_div_atTop :
    Tendsto (fun x : ℝ ↦ (∫ t in (2 : ℝ)..x, (Real.log t ^ 2)⁻¹) * Real.log x / x)
      atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun x : ℝ ↦ Real.log x / √x) atTop (𝓝 0) := by
    refine ((_root_.isLittleO_log_rpow_atTop (r := 1 / 2)
      (by norm_num)).tendsto_div_nhds_zero).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x _
    rw [Real.sqrt_eq_rpow]
  refine squeeze_zero' (g := fun x : ℝ ↦ Real.log x / √x * (Real.log 2 ^ 2)⁻¹ + 4 / Real.log x)
    ?_ ?_ ?_
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    have hnn := integral_inv_log_pow_nonneg 2 one_lt_two (by linarith : (2 : ℝ) ≤ x)
    positivity
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    have hsqx : √x * √x = x := Real.mul_self_sqrt hx0.le
    have hbound := integral_inv_log_sq_le hx
    rw [div_le_iff₀ hx0]
    have hexp : (Real.log x / √x * (Real.log 2 ^ 2)⁻¹ + 4 / Real.log x) * x =
        (√x / Real.log 2 ^ 2 + 4 * x / Real.log x ^ 2) * Real.log x := by
      field_simp
      nlinarith [hsqx]
    rw [hexp]
    exact mul_le_mul_of_nonneg_right hbound hlogx.le
  · have h₁ : Tendsto (fun x : ℝ ↦ Real.log x / √x * (Real.log 2 ^ 2)⁻¹) atTop (𝓝 0) := by
      simpa using hsqrt.mul_const ((Real.log 2 ^ 2)⁻¹)
    have h₂ : Tendsto (fun x : ℝ ↦ (4 : ℝ) / Real.log x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    simpa using h₁.add h₂

/-- **The logarithmic integral is asymptotic to `x / log x`**, in quotient form. -/
theorem tendsto_logIntegral_mul_log_div_atTop :
    Tendsto (fun x : ℝ ↦ logIntegral x * Real.log x / x) atTop (𝓝 1) := by
  have hlog : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hmain : Tendsto (fun x : ℝ ↦ 1 - 2 / Real.log 2 * (Real.log x / x) +
      (∫ t in (2 : ℝ)..x, (Real.log t ^ 2)⁻¹) * Real.log x / x) atTop (𝓝 1) := by
    have hone : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h := (hone.sub (hlog.const_mul (2 / Real.log 2))).add
      tendsto_integral_inv_log_sq_mul_log_div_atTop
    simpa using h
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  rw [logIntegral_eq_div_log_sub_add hx]
  field_simp

/-- **`Li x` is asymptotically equivalent to `x / log x`.** -/
theorem logIntegral_isEquivalent_div_log :
    logIntegral ~[atTop] fun x : ℝ ↦ x / Real.log x := by
  refine (isEquivalent_iff_tendsto_one ?_).mpr ?_
  · filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    positivity
  · refine tendsto_logIntegral_mul_log_div_atTop.congr' ?_
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with x _
    rw [Pi.div_apply, div_div_eq_mul_div]

/-! ### A weighted remainder integral

The integral `∫ t in 2..x, f t / (t * log t ^ 2)` is what Abel summation leaves behind when a
logarithmically weighted counting function is converted into an unweighted one.  It is negligible
on the scale `x / log x` as soon as `f` grows at most linearly. -/

/-- **The Chebyshev scale `x / log x` diverges.**  Equivalently, a constant is `o (x / log x)`. -/
theorem tendsto_div_log_atTop : Tendsto (fun x : ℝ ↦ x / Real.log x) atTop atTop := by
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  simp only [id_eq] at hlog
  have h : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hlog ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (Real.log_pos hx) (by linarith)
  exact h.inv_tendsto_nhdsGT_zero.congr fun x ↦ inv_div _ _

/-- A constant is `o (x / log x)`, because that scale diverges. -/
theorem isLittleO_const_div_log (c : ℝ) :
    (fun _ : ℝ ↦ c) =o[atTop] fun x : ℝ ↦ x / Real.log x :=
  isLittleO_const_left.mpr <| Or.inr <|
    (tendsto_abs_atTop_atTop.comp tendsto_div_log_atTop).congr fun _ ↦ (Real.norm_eq_abs _).symm

/-- An error of `o (x / log x)` relative to `δ Li x` gives the ratio limit `f x / (x / log x) → δ`,
since `Li x ~ x / log x`. -/
theorem tendsto_div_div_log_of_isLittleO_logIntegral {f : ℝ → ℝ} {δ : ℝ}
    (h : (fun x ↦ f x - δ * logIntegral x) =o[atTop] fun x : ℝ ↦ x / Real.log x) :
    Tendsto (fun x : ℝ ↦ f x / (x / Real.log x)) atTop (𝓝 δ) := by
  have h' : (fun x ↦ f x - δ * (x / Real.log x)) =o[atTop] fun x : ℝ ↦ x / Real.log x :=
    (h.add (logIntegral_isEquivalent_div_log.isLittleO.const_mul_left δ)).congr_left
      fun x ↦ by simp only [Pi.sub_apply]; ring
  exact (isLittleO_sub_mul_iff_tendsto_div (tendsto_div_log_atTop.eventually_ne_atTop 0)).mp h'

/-- `∫ t in 2..x, (log t ^ 2)⁻¹` is `o (x / log x)`; this is
`TauCeti.Real.tendsto_integral_inv_log_sq_mul_log_div_atTop` read as an `IsLittleO`. -/
theorem isLittleO_integral_inv_log_sq :
    (fun x : ℝ ↦ ∫ t in (2 : ℝ)..x, (Real.log t ^ 2)⁻¹) =o[atTop] fun x : ℝ ↦ x / Real.log x := by
  refine (isLittleO_iff_tendsto' ?_).mpr ?_
  · filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx hzero
    exact absurd hzero (div_pos (by linarith) (Real.log_pos (by linarith))).ne'
  · exact tendsto_integral_inv_log_sq_mul_log_div_atTop.congr fun x ↦
      (div_div_eq_mul_div _ _ _).symm

/-- The weight `(t * log t ^ 2)⁻¹` is continuous to the right of `1`, so it preserves interval
integrability there. -/
theorem intervalIntegrable_div_mul_log_sq {f : ℝ → ℝ} {a b : ℝ} (ha : 1 < a) (hb : 1 < b)
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t ↦ f t / (t * Real.log t ^ 2)) volume a b := by
  simp_rw [div_eq_mul_inv]
  refine hf.mul_continuousOn fun t ht ↦ ?_
  rw [mem_uIcc] at ht
  have h1 : 1 < t := by rcases ht with h | h; exacts [ha.trans_le h.1, hb.trans_le h.1]
  have h0 : t ≠ 0 := by linarith
  have hne : t * Real.log t ^ 2 ≠ 0 :=
    (mul_pos (by linarith) (pow_pos (Real.log_pos h1) 2)).ne'
  fun_prop

/-- Splitting at a cutoff `T` beyond which `|f t| ≤ c t`, the weighted integral of `f` is bounded
by its own initial segment plus `c` times the integral of `(log t ^ 2)⁻¹`. -/
private theorem abs_integral_div_mul_log_sq_le {f : ℝ → ℝ} {c T x : ℝ} (hT2 : 2 ≤ T) (hTx : T ≤ x)
    (hc0 : 0 ≤ c) (hf_int : ∀ y, 2 ≤ y → IntervalIntegrable f volume 2 y)
    (hbound : ∀ t, T ≤ t → |f t| ≤ c * t) :
    |∫ t in (2 : ℝ)..x, f t / (t * Real.log t ^ 2)| ≤
      |∫ t in (2 : ℝ)..T, f t / (t * Real.log t ^ 2)| +
        c * ∫ t in (2 : ℝ)..x, (Real.log t ^ 2)⁻¹ := by
  have h2x : (2 : ℝ) ≤ x := hT2.trans hTx
  have hint : IntervalIntegrable f volume T x := (hf_int x h2x).mono_set <| by
    rw [uIcc_of_le hTx, uIcc_of_le h2x]; exact Icc_subset_Icc hT2 le_rfl
  have htail : |∫ t in T..x, f t / (t * Real.log t ^ 2)| ≤
      c * ∫ t in T..x, (Real.log t ^ 2)⁻¹ := by
    calc |∫ t in T..x, f t / (t * Real.log t ^ 2)|
        ≤ ∫ t in T..x, |f t / (t * Real.log t ^ 2)| :=
          intervalIntegral.abs_integral_le_integral_abs hTx
      _ ≤ ∫ t in T..x, c * (Real.log t ^ 2)⁻¹ := by
          refine intervalIntegral.integral_mono_on hTx
            (intervalIntegrable_div_mul_log_sq (by linarith) (by linarith) hint).abs
            ((intervalIntegrable_inv_log_pow 2 (by linarith) (by linarith)).const_mul c)
            fun t ht ↦ ?_
          have h2t : (2 : ℝ) ≤ t := hT2.trans ht.1
          have hpos : 0 < t * Real.log t ^ 2 :=
            mul_pos (by linarith) (pow_pos (Real.log_pos (by linarith)) 2)
          rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
          have hrw : c * (Real.log t ^ 2)⁻¹ * (t * Real.log t ^ 2) = c * t := by
            have : Real.log t ≠ 0 := (Real.log_pos (by linarith)).ne'
            field_simp
          rw [hrw]
          exact hbound t ht.1
      _ = c * ∫ t in T..x, (Real.log t ^ 2)⁻¹ := intervalIntegral.integral_const_mul _ _
  have hJ : (∫ t in T..x, (Real.log t ^ 2)⁻¹) ≤ ∫ t in (2 : ℝ)..x, (Real.log t ^ 2)⁻¹ := by
    linarith [integral_inv_log_pow_nonneg 2 one_lt_two hT2,
      intervalIntegral.integral_add_adjacent_intervals
        (a := (2 : ℝ)) (b := T) (c := x) (f := fun t : ℝ ↦ (Real.log t ^ 2)⁻¹)
        (intervalIntegrable_inv_log_pow 2 one_lt_two (by linarith))
        (intervalIntegrable_inv_log_pow 2 (by linarith) (by linarith))]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_div_mul_log_sq one_lt_two (by linarith) (hf_int T hT2))
    (intervalIntegrable_div_mul_log_sq (by linarith) (by linarith) hint)]
  calc |(∫ t in (2 : ℝ)..T, f t / (t * Real.log t ^ 2)) +
          ∫ t in T..x, f t / (t * Real.log t ^ 2)|
      ≤ |∫ t in (2 : ℝ)..T, f t / (t * Real.log t ^ 2)| +
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
  -- Both summands of `abs_integral_div_mul_log_sq_le` are `o (x / log x)`.
  have hconst := isLittleO_const_div_log |∫ t in (2 : ℝ)..T, f t / (t * Real.log t ^ 2)|
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
    _ ≤ _ := abs_integral_div_mul_log_sq_le hT2 hx hc0 hf_int hbound
    _ ≤ ε / 2 * ‖x / Real.log x‖ + ε / 2 * ‖x / Real.log x‖ := add_le_add h1 h2
    _ = ε * ‖x / Real.log x‖ := by ring

/-! ### Behavior below `1`, power substitution, and the de la Vallée Poussin scale -/

/-- At and below the nonintegrable singularity `x = 1`, the offset logarithmic integral vanishes
by the Bochner convention `MeasureTheory.integral_undef`. -/
theorem logIntegral_of_le_one {x : ℝ} (hx : x ≤ 1) : logIntegral x = 0 := by
  rw [logIntegral_def]
  refine intervalIntegral.integral_undef ?_
  refine not_intervalIntegrable_of_sub_inv_isBigO_punctured (c := 1) ?_ (by linarith)
    (by rw [uIcc_of_ge (by linarith)]; exact ⟨hx, one_lt_two.le⟩)
  refine IsBigO.of_bound 2 ?_
  filter_upwards [mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    ⟨Ioo (1 / 2 : ℝ) 2, Ioo_mem_nhds (by norm_num) (by norm_num), Subset.rfl⟩] with t ⟨ht, hne⟩
  have ht0 : 0 < t := by linarith [ht.1]
  have hlog_ne : Real.log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one ht0 hne
  have hle : |Real.log t| ≤ 2 * |t - 1| := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hlog_inv : Real.log t⁻¹ ≤ t⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr ht0)
      rw [Real.log_inv] at hlog_inv
      rw [abs_of_neg (Real.log_neg ht0 hlt), abs_of_neg (sub_neg.mpr hlt)]
      have : t⁻¹ - 1 = (1 - t) / t := by field_simp
      rw [this, le_div_iff₀ ht0] at hlog_inv
      nlinarith [ht.1]
    · rw [abs_of_pos (Real.log_pos hgt), abs_of_pos (sub_pos.mpr hgt)]
      linarith [Real.log_le_sub_one_of_pos ht0]
  have hp1 : 0 < |Real.log t| := abs_pos.mpr hlog_ne
  have hp2 : 0 < |t - 1| := abs_pos.mpr (sub_ne_zero.mpr hne)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_inv, inv_eq_one_div, inv_eq_one_div,
    mul_one_div, div_le_div_iff₀ hp2 hp1]
  linarith

/-- Chain-rule derivative of `x ↦ Li (x ^ β)` on `(1, ∞)` for `β > 0`. -/
theorem hasDerivAt_logIntegral_rpow {β x : ℝ} (hβ : 0 < β) (hx : 1 < x) :
    HasDerivAt (fun t : ℝ ↦ logIntegral (t ^ β)) (x ^ (β - 1) / Real.log x) x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hxβ : 1 < x ^ β := Real.one_lt_rpow hx hβ
  have hd : HasDerivAt (fun t : ℝ ↦ logIntegral (t ^ β))
      ((Real.log (x ^ β))⁻¹ * (β * x ^ (β - 1))) x :=
    HasDerivAt.comp x (hasDerivAt_logIntegral hxβ)
      (Real.hasDerivAt_rpow_const (p := β) (Or.inl hx0.ne'))
  refine hd.congr_deriv ?_
  rw [Real.log_rpow hx0]
  have hβ0 : β ≠ 0 := hβ.ne'
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  field_simp

/-- **Power substitution in the logarithmic integral.** For `β > 0` and `a, b > 1`,
`∫ t in a..b, t ^ (β - 1) / log t = Li (b ^ β) - Li (a ^ β)` via `u = t ^ β`. -/
theorem integral_rpow_sub_one_div_log {β a b : ℝ} (hβ : 0 < β) (ha : 1 < a) (hb : 1 < b) :
    (∫ t in a..b, t ^ (β - 1) / Real.log t) = logIntegral (b ^ β) - logIntegral (a ^ β) := by
  have h1 : ∀ t ∈ uIcc a b, 1 < t := fun t ht ↦ by
    rcases mem_uIcc.mp ht with h | h <;> linarith [h.1]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hasDerivAt_logIntegral_rpow hβ (h1 t ht)) ?_
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
  have ht1 := h1 t ht
  exact ContinuousAt.continuousWithinAt <|
    (Real.continuousAt_rpow_const t (β - 1) (Or.inl (zero_lt_one.trans ht1).ne')).div
      (Real.continuousAt_log (zero_lt_one.trans ht1).ne') (Real.log_pos ht1).ne'

/-- **Abel-summation identity for a power secondary term.** Integrating the derivative of
`t ↦ t ^ β / (β log t)` on `[2, x]` matches the boundary and integral terms that Abel summation
produces from `t ^ β / β` with `Li (x ^ β) - Li (2 ^ β)` up to the base-point constant. -/
theorem rpow_div_mul_log_add_integral_eq_logIntegral_rpow {β x : ℝ} (hβ : 0 < β) (hx : 1 < x) :
    x ^ β / (β * Real.log x) + (∫ t in (2 : ℝ)..x, (t ^ β / β) / (t * Real.log t ^ 2)) =
      logIntegral (x ^ β) - logIntegral (2 ^ β) + 2 ^ β / (β * Real.log 2) := by
  have h1 : ∀ t ∈ uIcc (2 : ℝ) x, 1 < t := fun t ht ↦ by
    rcases mem_uIcc.mp ht with h | h <;> linarith [h.1]
  have hd : ∀ t ∈ uIcc (2 : ℝ) x, HasDerivAt (fun u : ℝ ↦ u ^ β / (β * Real.log u))
      (t ^ (β - 1) / Real.log t - (t ^ β / β) / (t * Real.log t ^ 2)) t := fun t ht ↦ by
    have ht1 := h1 t ht
    have ht0 : 0 < t := zero_lt_one.trans ht1
    have hlog : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    have hβ0 : β ≠ 0 := hβ.ne'
    have hq := (Real.hasDerivAt_rpow_const (p := β) (Or.inl ht0.ne')).div
      ((Real.hasDerivAt_log ht0.ne').const_mul β) (mul_ne_zero hβ0 hlog)
    exact hq.congr_deriv (by field_simp)
  have hi1 : IntervalIntegrable (fun t : ℝ ↦ t ^ (β - 1) / Real.log t) volume 2 x := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    have ht1 := h1 t ht
    exact (Real.continuousAt_rpow_const t (β - 1) (Or.inl (zero_lt_one.trans ht1).ne')).div
      (Real.continuousAt_log (zero_lt_one.trans ht1).ne') (Real.log_pos ht1).ne'
  have hi2 : IntervalIntegrable (fun t : ℝ ↦ (t ^ β / β) / (t * Real.log t ^ 2)) volume 2 x :=
    intervalIntegrable_div_mul_log_sq one_lt_two hx <|
      ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt <|
        (Real.continuousAt_rpow_const t β (Or.inl (zero_lt_one.trans (h1 t ht)).ne')).div_const β
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hi1.sub hi2)
  rw [intervalIntegral.integral_sub hi1 hi2, integral_rpow_sub_one_div_log hβ one_lt_two hx] at hFTC
  linarith

/-- A quadratic expression `u * (a * u - c)` with `a > 0` tends to `+∞` as `u → +∞`. -/
private theorem tendsto_mul_linear_atTop {a : ℝ} (ha : 0 < a) (c : ℝ) :
    Tendsto (fun u : ℝ ↦ u * (a * u - c)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨max 1 ((|b| + |c| + 1) / a), fun u hu ↦ ?_⟩
  have hu1 : 1 ≤ u := le_of_max_le_left hu
  have hu2 : (|b| + |c| + 1) / a ≤ u := le_of_max_le_right hu
  have hua : |b| + |c| + 1 ≤ u * a := (div_le_iff₀ ha).mp hu2
  nlinarith [le_abs_self b, le_abs_self c, abs_nonneg b, abs_nonneg c]

/-- The de la Vallée Poussin scale `x * exp (-c * √log x)` tends to infinity for every real `c`. -/
theorem tendsto_mul_exp_neg_mul_sqrt_log_atTop (c : ℝ) :
    Tendsto (fun x : ℝ ↦ x * Real.exp (-c * √(Real.log x))) atTop atTop := by
  have hsqrt : Tendsto (fun x : ℝ ↦ √(Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hquad : Tendsto (fun u : ℝ ↦ u * (1 * u - c)) atTop atTop :=
    tendsto_mul_linear_atTop zero_lt_one c
  refine (Real.tendsto_exp_atTop.comp (hquad.comp hsqrt)).congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  rw [Function.comp_apply, Function.comp_apply]
  conv_rhs => enter [1]; rw [← Real.exp_log hx0]
  rw [← Real.exp_add]
  congr 1
  nlinarith [Real.sq_sqrt hlog]

/-- A sublinear power `x ^ β` with `β < 1` is `o(x * exp (-c * √log x))` for every real `c`. -/
theorem isLittleO_rpow_mul_exp_neg_mul_sqrt_log {β : ℝ} (hβ : β < 1) (c : ℝ) :
    (fun x : ℝ ↦ x ^ β) =o[atTop] fun x : ℝ ↦ x * Real.exp (-c * √(Real.log x)) := by
  have hsqrt : Tendsto (fun x : ℝ ↦ √(Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hquad := tendsto_mul_linear_atTop (sub_pos.mpr hβ) c
  have hlim : Tendsto (fun x : ℝ ↦ Real.exp (-(√(Real.log x) * ((1 - β) * √(Real.log x) - c))))
      atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (hquad.comp hsqrt))
  refine (isLittleO_iff_tendsto' ?_).mpr (hlim.congr' ?_)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx h0
    exact absurd h0 (mul_pos (by linarith) (Real.exp_pos _)).ne'
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
    rw [Real.rpow_def_of_pos hx0]
    conv_rhs => enter [2, 1]; rw [← Real.exp_log hx0]
    rw [← Real.exp_add, ← Real.exp_sub]
    congr 1
    nlinarith [Real.sq_sqrt hlog]

/-- For `β < 1`, `Li (x ^ β)` is absorbed into `o(x * exp (-c * √log x))` for every real `c`. -/
theorem isLittleO_logIntegral_rpow_mul_exp_neg_mul_sqrt_log {β : ℝ} (hβ : β < 1) (c : ℝ) :
    (fun x : ℝ ↦ logIntegral (x ^ β)) =o[atTop] fun x : ℝ ↦ x * Real.exp (-c * √(Real.log x)) := by
  rcases le_or_gt β 0 with hβ0 | hβ0
  · refine (isLittleO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact (logIntegral_of_le_one (Real.rpow_le_one_of_one_le_of_nonpos hx hβ0)).symm
  · have hcomp : (fun x : ℝ ↦ logIntegral (x ^ β)) =O[atTop] fun x : ℝ ↦ x ^ β / Real.log (x ^ β) :=
      logIntegral_isEquivalent_div_log.isBigO.comp_tendsto (tendsto_rpow_atTop hβ0)
    have hdom : (fun x : ℝ ↦ x ^ β / Real.log (x ^ β)) =O[atTop] fun x : ℝ ↦ x ^ β := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [(tendsto_rpow_atTop hβ0).eventually_ge_atTop (Real.exp 1),
        eventually_gt_atTop (0 : ℝ)] with x hx hx0
      have hlog1 : 1 ≤ Real.log (x ^ β) := by
        simpa [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hx
      rw [one_mul, Real.norm_of_nonneg (div_nonneg (Real.rpow_nonneg hx0.le β) (by linarith)),
        Real.norm_of_nonneg (Real.rpow_nonneg hx0.le β)]
      exact div_le_self (Real.rpow_nonneg hx0.le β) hlog1
    exact (hcomp.trans hdom).trans_isLittleO (isLittleO_rpow_mul_exp_neg_mul_sqrt_log hβ c)

/-- Middle-segment bound on `[B, y]` with `y = x * exp (-(2 |c| + 1) * √log x)`. -/
private theorem abs_integral_div_mul_log_sq_mid_le {f : ℝ → ℝ} {c M B x : ℝ}
    (hB2 : 2 ≤ B) (hM : 0 ≤ M) (hx0 : 0 < x)
    (hyB : B ≤ x * Real.exp (-(2 * |c| + 1) * √(Real.log x)))
    (hint1 : IntervalIntegrable (fun t ↦ f t / (t * Real.log t ^ 2)) volume B
      (x * Real.exp (-(2 * |c| + 1) * √(Real.log x))))
    (hbound : ∀ t, B ≤ t → |f t| ≤ M * (t * Real.exp (-c * √(Real.log t)))) :
    |∫ t in B..(x * Real.exp (-(2 * |c| + 1) * √(Real.log x))), f t / (t * Real.log t ^ 2)| ≤
      (M / Real.log 2 ^ 2 * Real.exp (-√(Real.log x))) * (x * Real.exp (-c * √(Real.log x))) := by
  set y := x * Real.exp (-(2 * |c| + 1) * √(Real.log x))
  have hyx : y ≤ x := mul_le_of_le_one_right hx0.le <|
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith [abs_nonneg c])
      (Real.sqrt_nonneg _))
  calc |∫ t in B..y, f t / (t * Real.log t ^ 2)|
      ≤ ∫ t in B..y, M * Real.exp (|c| * √(Real.log x)) / Real.log 2 ^ 2 := by
        refine (intervalIntegral.abs_integral_le_integral_abs hyB).trans
          (intervalIntegral.integral_mono_on hyB hint1.abs intervalIntegrable_const fun t ht ↦ ?_)
        have ht2 : 2 ≤ t := hB2.trans ht.1
        have hst : √(Real.log t) ≤ √(Real.log x) :=
          Real.sqrt_le_sqrt (Real.log_le_log (by linarith) (ht.2.trans hyx))
        have hexp : Real.exp (-c * √(Real.log t)) ≤ Real.exp (|c| * √(Real.log x)) :=
          Real.exp_le_exp.mpr
            (by nlinarith [neg_le_abs c, Real.sqrt_nonneg (Real.log t), abs_nonneg c])
        rw [abs_div, abs_of_pos (mul_pos (by linarith) (pow_pos (Real.log_pos (by linarith)) 2))]
        calc |f t| / (t * Real.log t ^ 2)
            ≤ M * (t * Real.exp (-c * √(Real.log t))) / (t * Real.log t ^ 2) := by
              gcongr; exact hbound t ht.1
          _ = M * Real.exp (-c * √(Real.log t)) / Real.log t ^ 2 := by
              rw [mul_left_comm, mul_div_mul_left _ _ (by linarith)]
          _ ≤ M * Real.exp (|c| * √(Real.log x)) / Real.log 2 ^ 2 := by gcongr
    _ ≤ y * (M * Real.exp (|c| * √(Real.log x)) / Real.log 2 ^ 2) := by
        simp only [intervalIntegral.integral_const, smul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ ≤ (M / Real.log 2 ^ 2 * Real.exp (-√(Real.log x))) * (x * Real.exp (-c * √(Real.log x))) := by
        have hexp : Real.exp (-(2 * |c| + 1) * √(Real.log x) + |c| * √(Real.log x)) ≤
            Real.exp (-√(Real.log x) + -c * √(Real.log x)) :=
          Real.exp_le_exp.mpr (by nlinarith [le_abs_self c, Real.sqrt_nonneg (Real.log x)])
        calc y * (M * Real.exp (|c| * √(Real.log x)) / Real.log 2 ^ 2)
            = x * (M / Real.log 2 ^ 2) *
                Real.exp (-(2 * |c| + 1) * √(Real.log x) + |c| * √(Real.log x)) := by
              simp only [y, Real.exp_add]; ring
          _ ≤ x * (M / Real.log 2 ^ 2) * Real.exp (-√(Real.log x) + -c * √(Real.log x)) := by
              gcongr
          _ = (M / Real.log 2 ^ 2 * Real.exp (-√(Real.log x))) *
                (x * Real.exp (-c * √(Real.log x))) := by
              rw [Real.exp_add]; ring

/-- Upper-segment bound on `[y, x]` with `y = x * exp (-(2 |c| + 1) * √log x)`. -/
private theorem abs_integral_div_mul_log_sq_upper_le {f : ℝ → ℝ} {c M B x : ℝ}
    (hB2 : 2 ≤ B) (hM : 0 ≤ M) (hx0 : 0 < x)
    (hyB : B ≤ x * Real.exp (-(2 * |c| + 1) * √(Real.log x)))
    (hlogA : 2 * (2 * |c| + 1) ≤ √(Real.log x))
    (hint2 : IntervalIntegrable (fun t ↦ f t / (t * Real.log t ^ 2)) volume
      (x * Real.exp (-(2 * |c| + 1) * √(Real.log x))) x)
    (hbound : ∀ t, B ≤ t → |f t| ≤ M * (t * Real.exp (-c * √(Real.log t)))) :
    |∫ t in (x * Real.exp (-(2 * |c| + 1) * √(Real.log x)))..x, f t / (t * Real.log t ^ 2)| ≤
      (4 * M * Real.exp (|c| * (2 * |c| + 1)) / Real.log x ^ 2) *
        (x * Real.exp (-c * √(Real.log x))) := by
  set A := 2 * |c| + 1
  set y := x * Real.exp (-A * √(Real.log x))
  have hA0 : 0 ≤ A := by positivity
  have hy2 : 2 ≤ y := hB2.trans hyB
  have hyx : y ≤ x := mul_le_of_le_one_right hx0.le <|
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.sqrt_nonneg _))
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogy : Real.log y = Real.log x - A * √(Real.log x) := by
    rw [Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
  calc |∫ t in y..x, f t / (t * Real.log t ^ 2)|
      ≤ ∫ t in y..x, M * Real.exp (|c| * A - c * √(Real.log x)) / (Real.log x / 2) ^ 2 := by
        refine (intervalIntegral.abs_integral_le_integral_abs hyx).trans
          (intervalIntegral.integral_mono_on hyx hint2.abs intervalIntegrable_const fun t ht ↦ ?_)
        have ht2 : 2 ≤ t := hy2.trans ht.1
        have hlogyt : Real.log y ≤ Real.log t := Real.log_le_log (by linarith) ht.1
        have hlogt_half : Real.log x / 2 ≤ Real.log t := by
          nlinarith [hlogyt, hlogy, Real.sq_sqrt hlogx.le, Real.sqrt_nonneg (Real.log x)]
        have hsqrt_lb : √(Real.log x) - A ≤ √(Real.log t) :=
          Real.le_sqrt_of_sq_le
            (by nlinarith [hlogyt, hlogy, Real.sq_sqrt hlogx.le, hA0, hlogA])
        have hsqrt_ub : √(Real.log t) ≤ √(Real.log x) :=
          Real.sqrt_le_sqrt (Real.log_le_log (by linarith) ht.2)
        have hexp : Real.exp (-c * √(Real.log t)) ≤ Real.exp (|c| * A - c * √(Real.log x)) := by
          refine Real.exp_le_exp.mpr ?_
          have h1 : (-c) * (√(Real.log t) - √(Real.log x)) ≤
              |-c| * |√(Real.log t) - √(Real.log x)| := by
            rw [← abs_mul]; exact le_abs_self _
          have h2 : |-c| * |√(Real.log t) - √(Real.log x)| ≤ |c| * A := by
            rw [abs_neg]
            exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_nonneg c)
          linarith
        rw [abs_div, abs_of_pos (mul_pos (by linarith) (pow_pos (Real.log_pos (by linarith)) 2))]
        calc |f t| / (t * Real.log t ^ 2)
            ≤ M * (t * Real.exp (-c * √(Real.log t))) / (t * Real.log t ^ 2) := by
              gcongr; exact hbound t (hyB.trans ht.1)
          _ = M * Real.exp (-c * √(Real.log t)) / Real.log t ^ 2 := by
              rw [mul_left_comm, mul_div_mul_left _ _ (by linarith)]
          _ ≤ M * Real.exp (|c| * A - c * √(Real.log x)) / (Real.log x / 2) ^ 2 := by gcongr
    _ ≤ x * (M * Real.exp (|c| * A - c * √(Real.log x)) / (Real.log x / 2) ^ 2) := by
        simp only [intervalIntegral.integral_const, smul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = (4 * M * Real.exp (|c| * A) / Real.log x ^ 2) * (x * Real.exp (-c * √(Real.log x))) := by
        rw [sub_eq_add_neg, Real.exp_add]
        field_simp; ring

/-- Combined bound on `[B, x]` by splitting at `y = x * exp (-A * √log x)`. -/
private theorem abs_integral_div_mul_log_sq_tail_le {f : ℝ → ℝ} {c B M x : ℝ}
    (hB2 : 2 ≤ B) (hM0 : 0 ≤ M) (hxB : B ≤ x)
    (hyB : B ≤ x * Real.exp (-(2 * |c| + 1) * √(Real.log x)))
    (hlogA : 2 * (2 * |c| + 1) ≤ √(Real.log x))
    (hintBx : IntervalIntegrable (fun t ↦ f t / (t * Real.log t ^ 2)) volume B x)
    (hbound : ∀ t, B ≤ t → |f t| ≤ M * (t * Real.exp (-c * √(Real.log t)))) :
    |∫ t in B..x, f t / (t * Real.log t ^ 2)| ≤
      (M / Real.log 2 ^ 2 * Real.exp (-√(Real.log x)) +
        4 * M * Real.exp (|c| * (2 * |c| + 1)) / Real.log x ^ 2) *
        (x * Real.exp (-c * √(Real.log x))) := by
  have hx0 : 0 < x := by linarith
  set y := x * Real.exp (-(2 * |c| + 1) * √(Real.log x))
  have hyx : y ≤ x := mul_le_of_le_one_right hx0.le <|
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith [abs_nonneg c])
      (Real.sqrt_nonneg _))
  have hint1 : IntervalIntegrable (fun t ↦ f t / (t * Real.log t ^ 2)) volume B y :=
    hintBx.mono_set (by rw [uIcc_of_le hyB, uIcc_of_le hxB]; exact Icc_subset_Icc_right hyx)
  have hint2 : IntervalIntegrable (fun t ↦ f t / (t * Real.log t ^ 2)) volume y x :=
    hintBx.mono_set (by rw [uIcc_of_le hyx, uIcc_of_le hxB]; exact Icc_subset_Icc_left hyB)
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
  linarith [abs_add_le (∫ t in B..y, f t / (t * Real.log t ^ 2))
    (∫ t in y..x, f t / (t * Real.log t ^ 2)),
    abs_integral_div_mul_log_sq_mid_le hB2 hM0 hx0 hyB hint1 hbound,
    abs_integral_div_mul_log_sq_upper_le hB2 hM0 hx0 hyB hlogA hint2 hbound]

/-- Auxiliary case of `isLittleO_integral_div_mul_log_sq_of_isBigO_exp_neg_mul_sqrt_log` when the
weighted integrand is interval integrable on `[2, x]` for every `x ≥ 2`. -/
private theorem isLittleO_integral_div_mul_log_sq_of_intervalIntegrable {f : ℝ → ℝ} {c : ℝ}
    (hint_all : ∀ x, 2 ≤ x → IntervalIntegrable (fun t ↦ f t / (t * Real.log t ^ 2)) volume 2 x)
    (hf : f =O[atTop] fun x : ℝ ↦ x * Real.exp (-c * √(Real.log x))) :
    (fun x : ℝ ↦ ∫ t in (2 : ℝ)..x, f t / (t * Real.log t ^ 2)) =o[atTop]
      fun x : ℝ ↦ x * Real.exp (-c * √(Real.log x)) := by
  obtain ⟨M, hM⟩ := hf.bound
  obtain ⟨B, hB⟩ := eventually_atTop.mp (hM.and (eventually_ge_atTop (2 : ℝ)))
  have hB2 : 2 ≤ B := (hB B le_rfl).2
  have hbound : ∀ t, B ≤ t → |f t| ≤ M * (t * Real.exp (-c * √(Real.log t))) := fun t ht ↦ by
    have ht0 : 0 ≤ t := by linarith
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg ht0, abs_of_pos (Real.exp_pos _)] using
      (hB t ht).1
  have hM0 : 0 ≤ M := nonneg_of_mul_nonneg_left
    ((abs_nonneg _).trans (hbound B le_rfl)) (mul_pos (by linarith) (Real.exp_pos _))
  set A := 2 * |c| + 1
  set C₀ := |∫ t in (2 : ℝ)..B, f t / (t * Real.log t ^ 2)|
  have hsqrt : Tendsto (fun x : ℝ ↦ √(Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hcoef : Tendsto (fun x : ℝ ↦ C₀ / (x * Real.exp (-c * √(Real.log x))) +
      (M / Real.log 2 ^ 2 * Real.exp (-√(Real.log x)) +
        4 * M * Real.exp (|c| * A) / Real.log x ^ 2)) atTop (𝓝 0) := by
    have h1 := tendsto_const_nhds (x := C₀).div_atTop (tendsto_mul_exp_neg_mul_sqrt_log_atTop c)
    have h2 : Tendsto (fun x : ℝ ↦ M / Real.log 2 ^ 2 * Real.exp (-√(Real.log x))) atTop (𝓝 0) := by
      simpa using (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hsqrt)).const_mul
        (M / Real.log 2 ^ 2)
    have h3 := tendsto_const_nhds (x := 4 * M * Real.exp (|c| * A)).div_atTop
      ((tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp Real.tendsto_log_atTop)
    simpa using h1.add (h2.add h3)
  refine (isLittleO_iff_tendsto' ?_).mpr (squeeze_zero_norm' ?_ hcoef)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx h0
    exact absurd h0 (mul_pos (by linarith) (Real.exp_pos _)).ne'
  · filter_upwards [(tendsto_mul_exp_neg_mul_sqrt_log_atTop A).eventually_ge_atTop B,
      hsqrt.eventually_ge_atTop (2 * A), eventually_ge_atTop B] with x hyB hlogA hxB
    have hscale : 0 < x * Real.exp (-c * √(Real.log x)) := mul_pos (by linarith) (Real.exp_pos _)
    have hintBx : IntervalIntegrable (fun t ↦ f t / (t * Real.log t ^ 2)) volume B x :=
      (hint_all x (hB2.trans hxB)).mono_set
        (by rw [uIcc_of_le hxB, uIcc_of_le (hB2.trans hxB)]; exact Icc_subset_Icc_left hB2)
    have htail := abs_integral_div_mul_log_sq_tail_le hB2 hM0 hxB
      (by simpa [A, neg_mul] using hyB) hlogA hintBx hbound
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hscale,
      ← intervalIntegral.integral_add_adjacent_intervals (hint_all B hB2) hintBx]
    have htri := abs_add_le (∫ t in (2 : ℝ)..B, f t / (t * Real.log t ^ 2))
      (∫ t in B..x, f t / (t * Real.log t ^ 2))
    rw [div_le_iff₀ hscale, right_distrib, div_mul_cancel₀ _ hscale.ne']
    linarith [htri, htail]

/-- **Weighted remainder integral on the de la Vallée Poussin scale.** If
`f = O(x * exp (-c * √log x))` at infinity, then `∫ t in 2..x, f t / (t * log t ^ 2)` is
`o(x * exp (-c * √log x))` with the same constant `c`. -/
theorem isLittleO_integral_div_mul_log_sq_of_isBigO_exp_neg_mul_sqrt_log {f : ℝ → ℝ} {c : ℝ}
    (hf : f =O[atTop] fun x : ℝ ↦ x * Real.exp (-c * √(Real.log x))) :
    (fun x : ℝ ↦ ∫ t in (2 : ℝ)..x, f t / (t * Real.log t ^ 2)) =o[atTop]
      fun x : ℝ ↦ x * Real.exp (-c * √(Real.log x)) := by
  by_cases hint_all :
      ∀ x, 2 ≤ x → IntervalIntegrable (fun t ↦ f t / (t * Real.log t ^ 2)) volume 2 x
  · exact isLittleO_integral_div_mul_log_sq_of_intervalIntegrable hint_all hf
  · obtain ⟨x₀, hnot⟩ := Classical.not_forall.mp hint_all
    rw [not_imp] at hnot
    obtain ⟨hx₀2, hnot⟩ := hnot
    refine (isLittleO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop x₀] with x hx
    symm
    refine intervalIntegral.integral_undef fun h ↦ hnot (h.mono_set ?_)
    rw [uIcc_of_le hx₀2, uIcc_of_le (hx₀2.trans hx)]
    exact Icc_subset_Icc_right hx

end TauCeti.Real
