/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.InvLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.SpecialFunctions.Integrals.InvLog
import TauCeti.Analysis.SpecialFunctions.Log.Asymptotics

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
the remaining integral is `o (x / log x)` (from
`TauCeti.Analysis.SpecialFunctions.Integrals.InvLog`). Splitting that integral at `√x` bounds it
by `√x / (log 2) ^ 2 + 4 * x / (log x) ^ 2`, and both terms are `o (x / log x)`.

## Main declarations

* `TauCeti.Real.logIntegral` — the offset logarithmic integral.
* `TauCeti.Real.hasDerivAt_logIntegral` — its derivative `(log x)⁻¹` for `x > 1`.
* `TauCeti.Real.le_logIntegral` — the elementary lower bound `(x - 2) / log x ≤ Li x`.
* `TauCeti.Real.logIntegral_eq_div_log_sub_add` — the antiderivative identity above.
* `TauCeti.Real.logIntegral_isEquivalent_div_log` — `Li x ~ x / log x` at infinity, with the
  quotient form `TauCeti.Real.tendsto_logIntegral_mul_log_div_atTop`.
* `TauCeti.Real.tendsto_div_div_log_of_isLittleO_logIntegral` — an `o (x / log x)` error
  relative to `δ Li x` gives `f x / (x / log x) → δ`.
* `TauCeti.Real.isLittleO_integral_div_mul_log_sq` — for `f` interval integrable above `2` and of
  at most linear growth, `∫ t in 2..x, f t / (t * log t ^ 2)` is `o (x / log x)`.
* `TauCeti.Real.integral_inv_log_sq_eq_logIntegral_sub_div_log_sub` — `∫ t in a..b, (log t ^ 2)⁻¹`
  is the increment of `x ↦ Li x - x / log x` from `a` to `b`.
* `TauCeti.Real.integral_div_mul_log_sq_eq_sub_add` — subtracting `δ t` from the integrand of
  `∫ t in a..b, F t / (t * log t ^ 2)` splits off `δ * ∫ t in a..b, (log t ^ 2)⁻¹`.
* `TauCeti.Real.integral_div_mul_log_sq_le_integral_div_log_sq`,
  `TauCeti.Real.neg_integral_div_log_sq_le_integral_div_mul_log_sq` — one-sided comparisons of
  `∫ t in a..b, f t / (t * log t ^ 2)` with `∫ t in a..b, g t / log t ^ 2` from `f t ≤ t g t` and
  `-(t g t) ≤ f t`.
* `TauCeti.Real.abs_integral_div_mul_log_sq_le_integral_div_log_sq`,
  `TauCeti.Real.abs_integral_div_mul_log_sq_le_sum` — explicit bounds: `|f t| ≤ t g t` on `[a, b]`
  bounds `|∫ t in a..b, f t / (t * log t ^ 2)|` by `∫ t in a..b, g t / log t ^ 2`, and linear bounds
  `|f t| ≤ c i * t` on the pieces of a partition bound it by increments of `x ↦ Li x - x / log x`.

## Use in prime counting

These are the analytic inputs to the transfer `ϑ(x) ∼ δx ⟹ π(x) ∼ δ Li(x)`,
`TauCeti.primeCount_asymptotic_of_primeTheta` in
`TauCeti/NumberTheory/ArithmeticDirichletSeries/Transfer.lean`. The weighted-remainder estimate
`TauCeti.Real.isLittleO_integral_div_mul_log_sq` is what absorbs the integral produced by Abel
summation there. The explicit bounds feed the transfer of explicit bounds for `θ` to explicit
bounds for `π - Li` in `TauCeti/NumberTheory/Chebyshev/ThetaTransfer.lean`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapters 7 and 18.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.
* A. Fiori, H. Kadiri, J. Swidinsky, *Sharper bounds for the error term in the prime number
  theorem*, Res. Number Theory 9 (2023), article 63, Lemma 19 (the bound on a partition).

Mathlib's `Mathlib/NumberTheory/Chebyshev.lean` carries out this estimate for the rational
Chebyshev function, in `Chebyshev.integral_theta_div_log_sq_isLittleO`; the argument for a general
integrand below follows the same split into a bounded initial segment and a linearly bounded tail.
-/

public section

open Asymptotics Filter MeasureTheory Set
open scoped Topology

namespace TauCeti.Real

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

/-- **The antiderivative identity for the logarithmic integral.** Integrating the derivative of
`t ↦ t / log t` from `2` to `x` writes `Li x` as `x / log x` plus a constant and a remainder
integral, which the asymptotic below shows is `o (x / log x)`. -/
theorem logIntegral_eq_div_log_sub_add {x : ℝ} (hx : 2 ≤ x) :
    logIntegral x =
      x / Real.log x - 2 / Real.log 2 + ∫ t in (2 : ℝ)..x, (Real.log t ^ 2)⁻¹ := by
  simpa only [logIntegral, pow_one, Nat.cast_one, one_mul] using
    integral_inv_log_pow_eq_sub_add 1 one_lt_two (one_lt_two.trans_le hx)

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
    have hbound := Real.integral_inv_log_pow_le_sqrt_add 2 (by linarith : (2 : ℝ) ≤ x)
    norm_num at hbound
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
`∫ t in a..b, (log t ^ 2)⁻¹` of the antiderivative identity. -/
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
    simpa only [div_eq_mul_inv, intervalIntegral.integral_const_mul] using
      abs_integral_div_mul_log_sq_le_integral_div_log_sq (g := fun _ ↦ c) (by linarith) hTx hint
        intervalIntegrable_const fun t ht ↦ (hbound t ht.1).trans_eq (mul_comm c t)
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
    _ ≤ _ := abs_integral_div_mul_log_sq_le hT2 hx hc0 hf_int hbound
    _ ≤ ε / 2 * ‖x / Real.log x‖ + ε / 2 * ‖x / Real.log x‖ := add_le_add h1 h2
    _ = ε * ‖x / Real.log x‖ := by ring

/-! ### Explicit bounds for integrals against the weight `(t log² t)⁻¹` -/

/-- The remainder integral of the antiderivative identity between two points to the right of `1`:
`∫ t in a..b, (log t ^ 2)⁻¹` is the increment of `x ↦ Li x - x / log x` from `a` to `b`. -/
theorem integral_inv_log_sq_eq_logIntegral_sub_div_log_sub {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    ∫ t in a..b, (Real.log t ^ 2)⁻¹ =
      logIntegral b - b / Real.log b - (logIntegral a - a / Real.log a) := by
  have hparts := integral_inv_log_pow_eq_sub_add 1 ha hb
  norm_num only [pow_one, Nat.cast_one, one_mul] at hparts
  have hLi : logIntegral b - logIntegral a = ∫ t in a..b, (Real.log t)⁻¹ := by
    simpa only [logIntegral_def, pow_one] using
      intervalIntegral.integral_interval_sub_left (intervalIntegrable_inv_log_pow 1 one_lt_two hb)
        (intervalIntegrable_inv_log_pow 1 one_lt_two ha)
  linarith

/-- **A linear bound on one interval.**  If `|f t| ≤ c t` on `[a, b]` with `1 < a ≤ b`, then
`|∫ t in a..b, f t / (t log² t)|` is at most `c` times the increment of `x ↦ Li x - x / log x`
from `a` to `b`. -/
theorem abs_integral_div_mul_log_sq_le_mul {f : ℝ → ℝ} {a b c : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (h : ∀ t ∈ Icc a b, |f t| ≤ c * t) :
    |∫ t in a..b, f t / (t * Real.log t ^ 2)| ≤
      c * (logIntegral b - b / Real.log b - (logIntegral a - a / Real.log a)) := by
  have hbound := abs_integral_div_mul_log_sq_le_integral_div_log_sq (g := fun _ ↦ c) ha hab hf
    intervalIntegrable_const fun t ht ↦ (h t ht).trans_eq (mul_comm c t)
  simp only [div_eq_mul_inv, intervalIntegral.integral_const_mul] at hbound
  rwa [integral_inv_log_sq_eq_logIntegral_sub_div_log_sub ha (ha.trans_le hab)] at hbound

/-- **Linear bounds on a partition.**  Let `s 0 ≤ s 1 ≤ ⋯ ≤ s N` with `1 < s 0`, and suppose
`|f t| ≤ c i * t` on each piece `[s i, s (i + 1)]`. Then `|∫ t in s 0..s N, f t / (t log² t)|` is
at most the sum over the pieces of `c i` times the increment of `x ↦ Li x - x / log x` across the
piece.

This is Lemma 19 of Fiori, Kadiri and Swidinsky. -/
theorem abs_integral_div_mul_log_sq_le_sum {f : ℝ → ℝ} {s c : ℕ → ℝ} {N : ℕ} (hs₀ : 1 < s 0)
    (hs : ∀ i < N, s i ≤ s (i + 1)) (hf : ∀ i < N, IntervalIntegrable f volume (s i) (s (i + 1)))
    (h : ∀ i < N, ∀ t ∈ Icc (s i) (s (i + 1)), |f t| ≤ c i * t) :
    |∫ t in s 0..s N, f t / (t * Real.log t ^ 2)| ≤
      ∑ i ∈ Finset.range N, c i * (logIntegral (s (i + 1)) - s (i + 1) / Real.log (s (i + 1)) -
        (logIntegral (s i) - s i / Real.log (s i))) := by
  have hs₁ : ∀ i ≤ N, 1 < s i := by
    intro i hi
    induction i with
    | zero => exact hs₀
    | succ i ih => exact (ih (by omega)).trans_le (hs i (by omega))
  rw [← intervalIntegral.sum_integral_adjacent_intervals fun i hi ↦
    intervalIntegrable_div_mul_log_sq (hs₁ i hi.le) (hs₁ (i + 1) hi) (hf i hi)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi ↦ ?_)
  rw [Finset.mem_range] at hi
  exact abs_integral_div_mul_log_sq_le_mul (hs₁ i hi.le) (hs i hi) (hf i hi) (h i hi)

end TauCeti.Real
