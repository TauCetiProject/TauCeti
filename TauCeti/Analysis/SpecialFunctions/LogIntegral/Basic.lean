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
the fundamental theorem of calculus applied to `t ↦ t / log t`, together with the estimate
`TauCeti.Real.tendsto_integral_inv_log_sq_mul_log_div_atTop` that the remaining integral is
`o (x / log x)` (from `TauCeti.Analysis.SpecialFunctions.Integrals.InvLog`).

## Main declarations

* `TauCeti.Real.logIntegral` — the offset logarithmic integral.
* `TauCeti.Real.hasDerivAt_logIntegral` — its derivative `(log x)⁻¹` for `x > 1`.
* `TauCeti.Real.le_logIntegral` — the elementary lower bound `(x - 2) / log x ≤ Li x`.
* `TauCeti.Real.logIntegral_eq_div_log_sub_add` — the antiderivative identity above.
* `TauCeti.Real.logIntegral_isEquivalent_div_log` — `Li x ~ x / log x` at infinity, with the
  quotient form `TauCeti.Real.tendsto_logIntegral_mul_log_div_atTop`.
* `TauCeti.Real.tendsto_div_div_log_of_isLittleO_logIntegral` — an `o (x / log x)` error
  relative to `δ Li x` gives `f x / (x / log x) → δ`.
* `TauCeti.Real.integral_inv_log_sq_eq_logIntegral_sub_div_log_sub` — `∫ t in a..b, (log t ^ 2)⁻¹`
  is the increment of `x ↦ Li x - x / log x` from `a` to `b`.
* `TauCeti.Real.abs_integral_div_mul_log_sq_le_mul`,
  `TauCeti.Real.abs_integral_div_mul_log_sq_le_sum` — explicit bounds: `|f t| ≤ c * t` on `[a, b]`
  or `|f t| ≤ c i * t` on the pieces of a partition bound `|∫ f t / (t * log t ^ 2)|` by
  increments of `x ↦ Li x - x / log x`.

## Use in prime counting

These are the analytic inputs to the transfer `ϑ(x) ∼ δx ⟹ π(x) ∼ δ Li(x)`,
`TauCeti.primeCount_asymptotic_of_primeTheta` in
`TauCeti/NumberTheory/ArithmeticDirichletSeries/Transfer.lean` (together with the weighted
remainder estimates in `TauCeti/Analysis/SpecialFunctions/Integrals/InvLog.lean`), and to the
transfer of explicit bounds for `θ` to explicit bounds for `π - Li` in
`TauCeti/NumberTheory/Chebyshev/ThetaTransfer.lean`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapters 7 and 18.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.
* A. Fiori, H. Kadiri, J. Swidinsky, *Sharper bounds for the error term in the prime number
  theorem*, Res. Number Theory 9 (2023), article 63, Lemma 19 (the bound on a partition).
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

/-- An error of `o (x / log x)` relative to `δ Li x` gives the ratio limit `f x / (x / log x) → δ`,
since `Li x ~ x / log x`. -/
theorem tendsto_div_div_log_of_isLittleO_logIntegral {f : ℝ → ℝ} {δ : ℝ}
    (h : (fun x ↦ f x - δ * logIntegral x) =o[atTop] fun x : ℝ ↦ x / Real.log x) :
    Tendsto (fun x : ℝ ↦ f x / (x / Real.log x)) atTop (𝓝 δ) := by
  have h' : (fun x ↦ f x - δ * (x / Real.log x)) =o[atTop] fun x : ℝ ↦ x / Real.log x :=
    (h.add (logIntegral_isEquivalent_div_log.isLittleO.const_mul_left δ)).congr_left
      fun x ↦ by simp only [Pi.sub_apply]; ring
  exact (isLittleO_sub_mul_iff_tendsto_div (tendsto_div_log_atTop.eventually_ne_atTop 0)).mp h'

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
