/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import TauCeti.Analysis.SpecialFunctions.LogIntegral.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import TauCeti.Analysis.Normed.Algebra.OneSubExpNegDivSelf.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.ExpIntegralSeries
import TauCeti.Analysis.SpecialFunctions.Integrals.LogMulExpNeg
import TauCeti.Analysis.SpecialFunctions.Log.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Log.Bounds

/-!
# The unoffset logarithmic integral

This file defines the unoffset logarithmic integral

```text
li x = γ + log |log x| + ∑_{n ≥ 1} (log x)ⁿ / (n · n!)
```

where `γ` is the Euler–Mascheroni constant, for real `x > 0`, `x ≠ 1` (the exponential integral
`Ei` evaluated at `log x`). Mathlib's `log` is `log |·|`, so `log (log x)` equals `log |log x|`
for every `x > 0` with `x ≠ 1`; for `x ≤ 0` and at `x = 1` the values are junk: in particular
`li 0 = li 1 = γ` (not `0`), and `li (-x) = li x` for `x < 0`.

Unlike the offset logarithmic integral `TauCeti.Real.logIntegral` (`Li x`, with `Li 2 = 0`), `li`
cannot be defined on `(1, ∞)` by a plain interval integral from `0` to `x` because `(log t)⁻¹`
has a nonintegrable singularity at `t = 1`. Defining `li` by the globally convergent series avoids
that singularity and lets the Cauchy principal value and exponential integral representations
(proved in `TauCeti.Analysis.SpecialFunctions.LogIntegral.PrincipalValue`) follow as theorems.

The function `li` is the normalisation of the logarithmic integral used in the explicit forms of
the prime number theorem of Schoenfeld, Büthe and later authors, for instance
`|π(x) - li x| < √x log x / (8π)` under the Riemann hypothesis. It differs from `Li x` by the
constant `li 2` on `(1, ∞)`, so that bounds stated with either normalisation convert into each
other.

Termwise differentiation of `liSeries` gives `(e^y - 1) / y` at `y = log x`
(`Real.tsum_pow_div_factorial_succ`), and the chain rule then gives `li' x = (log x)⁻¹` on `(0, 1)`
and on `(1, ∞)`. Hence `li` is an antiderivative of `(log t)⁻¹` on both intervals: it is strictly
decreasing on `(0, 1)`, strictly increasing on `(1, ∞)`, tends to `0` as `x → 0⁺`, to `-∞` at `1`
from either side, and to `+∞` at infinity. From `γ > 1 / 2` (Mathlib), `log (3 / 2) > 2 / 5`
(`Real.two_fifths_lt_log_three_halves`) and the first two terms of the series one gets
`li (3 / 2) > 0`, so `li` has exactly one zero in `(1, ∞)`, Soldner's constant, and it lies in
`(1, 3 / 2)`.

## Main declarations

* `TauCeti.Real.li`, `TauCeti.Real.li_def`, `TauCeti.Real.li_eq_add_log_abs`,
  `TauCeti.Real.li_zero`, `TauCeti.Real.li_one`, `TauCeti.Real.li_neg_eq` — the unoffset logarithmic
  integral and its normalization lemmas.
* `TauCeti.Real.liSeries`, `TauCeti.Real.liSeries_def`, `TauCeti.Real.li_eq_add_liSeries`,
  `TauCeti.Real.summable_liSeries`, `TauCeti.Real.hasSum_liSeries`,
  `TauCeti.Real.hasDerivAt_liSeries`, `TauCeti.Real.hasDerivAt_liSeries_of_ne_zero`,
  `TauCeti.Real.hasDerivAt_liSeries_zero`, `TauCeti.Real.continuous_liSeries`,
  `TauCeti.Real.liSeries_zero`, `TauCeti.Real.sum_range_le_liSeries` — the entire part
  `∑_{n ≥ 1} yⁿ / (n · n!)` and its calculus.
* `TauCeti.Real.hasDerivAt_li`, `TauCeti.Real.deriv_li`, `TauCeti.Real.differentiableAt_li`,
  `TauCeti.Real.continuousAt_li`, `TauCeti.Real.measurable_li` — derivative `(log x)⁻¹` and
  regularity of `li`.
* `TauCeti.Real.li_eq_add_log_neg_log_mul_add_integral`, `TauCeti.Real.tendsto_li_nhdsGT_zero` —
  closed-form identity on `(0, 1)` and `li x → 0` as `x → 0⁺`.
* `TauCeti.Real.integral_inv_log_eq_li_sub`, `TauCeti.Real.integral_inv_log_eq_li_sub_li`,
  `TauCeti.Real.integral_inv_log_eq_li_sub_li_of_lt_one` — endpoint-difference formula
  `∫ t in a..b, (log t)⁻¹ = li b - li a` on either branch `(0, 1)` or `(1, ∞)`.
* `TauCeti.Real.logIntegral_eq_li_sub_li_two`, `TauCeti.Real.li_eq_logIntegral_add_li_two` —
  the offset identity `Li x = li x - li 2` for `x > 1`.
* `TauCeti.Real.strictMonoOn_li`, `TauCeti.Real.strictAntiOn_li`, `TauCeti.Real.li_neg`,
  `TauCeti.Real.tendsto_tsum_log_pow_div_mul_factorial_nhds_one`,
  `TauCeti.Real.tendsto_li_nhdsNE_one`, `TauCeti.Real.tendsto_li_nhdsGT_one`,
  `TauCeti.Real.tendsto_li_nhdsLT_one`, `TauCeti.Real.tendsto_li_atTop` — monotonicity and
  boundary limits.
* `TauCeti.Real.li_pos`, `TauCeti.Real.li_two_pos`, `TauCeti.Real.li_ne_logIntegral`,
  `TauCeti.Real.lt_three_halves_of_li_eq_zero`, `TauCeti.Real.existsUnique_li_eq_zero` —
  positivity for `x ≥ 3 / 2` and Soldner's constant.

## References

* F. W. J. Olver et al., *NIST Digital Library of Mathematical Functions*, §§6.2, 6.6, and 6.13
  (Exponential, Logarithmic, Sine, and Cosine Integrals).
* H. Davenport, *Multiplicative Number Theory*, Chapters 7 and 18.
* L. Schoenfeld, *Sharper bounds for the Chebyshev functions θ(x) and ψ(x). II*, Math. Comp. 30
  (1976), 337–360, where `li` is the normalisation of the bounds under the Riemann hypothesis.
* M. Abramowitz and I. A. Stegun, *Handbook of Mathematical Functions*, §5.1, formulas 5.1.3
  and 5.1.10, for `li x = Ei (log x)` and the series of `Ei`.
-/

public section

namespace TauCeti.Real

open Filter MeasureTheory Set
open _root_.Real
open scoped Nat Topology

/-- The **unoffset logarithmic integral**
`li x = γ + log |log x| + ∑_{n ≥ 1} (log x)ⁿ / (n · n!)`, the exponential integral `Ei` at
`log x`.

For `0 < x < 1` it equals `∫ t in 0..x, (log t)⁻¹`, for `x > 1` it is the Cauchy principal value
of `∫₀ˣ dt / log t`, and it differs from the offset logarithmic integral `TauCeti.Real.logIntegral`
by `li 2` there (`TauCeti.Real.logIntegral_eq_li_sub_li_two`). Mathlib's `log` is `log |·|`, so
`log (log x)` is `log |log x|`; for `x ≤ 0` and at `x = 1` the values are junk (in particular
`li 0 = li 1 = γ`, and `li (-x) = li x`). -/
noncomputable def li (x : ℝ) : ℝ :=
  eulerMascheroniConstant + log (log x) +
    ∑' n : ℕ, log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))

/-- Defining equation of `TauCeti.Real.li`. -/
theorem li_def (x : ℝ) :
    li x = eulerMascheroniConstant + log (log x) +
      ∑' n : ℕ, log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := (rfl)

/-- Explicit absolute-value form of `TauCeti.Real.li`. -/
theorem li_eq_add_log_abs (x : ℝ) :
    li x = eulerMascheroniConstant + log |log x| +
      ∑' n : ℕ, log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
  rw [li_def, log_abs]

/-- `li 0` takes the junk value `γ`. -/
@[simp]
theorem li_zero : li 0 = eulerMascheroniConstant := by
  simp [li_def]

/-- `li 1` takes the junk value `γ`. -/
@[simp]
theorem li_one : li 1 = eulerMascheroniConstant := by
  simp [li_def]

/-- `li` is symmetric in sign (for `x < 0`, `li x` takes the junk value `li (-x)`). -/
@[simp]
theorem li_neg_eq (x : ℝ) : li (-x) = li x := by
  simp [li_def]

/-! ### The series `∑_{n ≥ 1} yⁿ / (n · n!)` -/

/-- The entire part `∑_{n ≥ 1} yⁿ / (n · n!)` of the exponential integral, so that
`li x = γ + log |log x| + liSeries (log x)`. -/
noncomputable def liSeries (y : ℝ) : ℝ :=
  ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))

/-- Defining equation of `TauCeti.Real.liSeries`. -/
theorem liSeries_def (y : ℝ) :
    liSeries y = ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := (rfl)

/-- `li x = γ + log |log x| + liSeries (log x)`. -/
theorem li_eq_add_liSeries (x : ℝ) :
    li x = eulerMascheroniConstant + log (log x) + liSeries (log x) := (rfl)

/-- The series `liSeries y` converges absolutely for every real `y`; at `y = log x` its terms are
those of `li_def`. -/
theorem summable_liSeries (y : ℝ) :
    Summable fun n : ℕ ↦ y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) :=
  summable_pow_div_mul_factorial y

/-- The series `∑_{n ≥ 1} yⁿ / (n · n!)` sums to `liSeries y`. -/
theorem hasSum_liSeries (y : ℝ) :
    HasSum (fun n : ℕ ↦ y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) (liSeries y) :=
  (summable_liSeries y).hasSum

/-- The termwise derivative `∑_{n ≥ 0} yⁿ / (n + 1)!` of `liSeries`. -/
theorem hasDerivAt_liSeries (y : ℝ) :
    HasDerivAt liSeries (∑' n : ℕ, y ^ n / ((n + 1)! : ℝ)) y := by
  set R : ℝ := |y| + 1
  have hR : 0 < R := by positivity
  unfold liSeries
  refine hasDerivAt_tsum_of_isPreconnected (u := fun n ↦ R ^ n / (n ! : ℝ))
    (g' := fun n z ↦ z ^ n / ((n + 1)! : ℝ))
    (Real.summable_pow_div_factorial R) Metric.isOpen_ball (convex_ball (0 : ℝ) R).isPreconnected
    (fun n z _ ↦ ?_) (fun n z hz ↦ ?_) (Metric.mem_ball_self hR) (by simp)
    (by simp [R])
  · have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    convert (hasDerivAt_pow (n + 1) z).div_const (((n : ℝ) + 1) * ((n + 1)! : ℝ)) using 1
    push_cast [Nat.factorial_succ, add_tsub_cancel_right]
    field_simp
  · have hz' : |z| ≤ R := by simpa [Real.dist_eq] using (Metric.mem_ball.1 hz).le
    have hf : (0 : ℝ) < n ! := mod_cast n.factorial_pos
    rw [norm_div, norm_pow, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
    exact div_le_div₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg z) hz' n) hf
      (mod_cast Nat.factorial_le n.le_succ)

/-- For `y ≠ 0`, the derivative of `liSeries` at `y` is `(e^y - 1) / y`. -/
theorem hasDerivAt_liSeries_of_ne_zero {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt liSeries ((exp y - 1) / y) y := by
  simpa [Real.tsum_pow_div_factorial_succ hy] using hasDerivAt_liSeries y

/-- The derivative of `liSeries` at `0` is `1`. -/
theorem hasDerivAt_liSeries_zero : HasDerivAt liSeries 1 0 := by
  convert hasDerivAt_liSeries 0 using 1
  rw [tsum_eq_single 0 fun n hn ↦ by simp [hn]]
  simp

/-- The series `liSeries` is continuous. -/
theorem continuous_liSeries : Continuous liSeries :=
  continuous_tsum_pow_div_mul_factorial

/-- The series `liSeries` vanishes at `0`. -/
@[simp]
theorem liSeries_zero : liSeries 0 = 0 := by
  simp [liSeries]

/-- The first `k` terms of `liSeries` bound it below for `y ≥ 0`. -/
theorem sum_range_le_liSeries {y : ℝ} (hy : 0 ≤ y) (k : ℕ) :
    ∑ n ∈ Finset.range k, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) ≤ liSeries y :=
  sum_range_le_tsum_pow_div_mul_factorial hy k

/-! ### Derivative, regularity, and behaviour at `0⁺` -/

/-- The unoffset logarithmic integral has derivative `(log x)⁻¹` at every `x > 0` with `x ≠ 1`. -/
theorem hasDerivAt_li {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) :
    HasDerivAt li (log x)⁻¹ x := by
  have hl : log x ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hx hx1
  have hlog := Real.hasDerivAt_log hx.ne'
  have h := ((hlog.log hl).const_add eulerMascheroniConstant).add
    ((hasDerivAt_liSeries_of_ne_zero hl).comp x hlog)
  rw [Real.exp_log hx] at h
  convert h using 1
  · ext y
    exact li_eq_add_liSeries y
  · field_simp
    ring

/-- The derivative of the unoffset logarithmic integral at `x > 0`, `x ≠ 1`. -/
@[simp]
theorem deriv_li {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) : deriv li x = (log x)⁻¹ :=
  (hasDerivAt_li hx hx1).deriv

/-- The unoffset logarithmic integral is differentiable at every `x > 0` with `x ≠ 1`. -/
@[fun_prop]
theorem differentiableAt_li {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) : DifferentiableAt ℝ li x :=
  (hasDerivAt_li hx hx1).differentiableAt

/-- The unoffset logarithmic integral is continuous at every `x > 0` with `x ≠ 1`. -/
@[fun_prop]
theorem continuousAt_li {x : ℝ} (hx : 0 < x) (hx1 : x ≠ 1) : ContinuousAt li x :=
  (hasDerivAt_li hx hx1).continuousAt

/-- `li` is measurable on `ℝ`. -/
@[fun_prop]
theorem measurable_li : Measurable li := by
  unfold li
  exact (measurable_const.add (measurable_log.comp measurable_log)).add
    (continuous_tsum_pow_div_mul_factorial.measurable.comp measurable_log)

/-- `li` is differentiable on `(0, 1)`. -/
theorem differentiableOn_li_Ioo : DifferentiableOn ℝ li (Ioo 0 1) :=
  fun _ hx ↦ (differentiableAt_li hx.1 hx.2.ne).differentiableWithinAt

/-- `li` is differentiable on `(1, ∞)`. -/
theorem differentiableOn_li_Ioi : DifferentiableOn ℝ li (Ioi 1) :=
  fun _ hx ↦ (differentiableAt_li (zero_lt_one.trans hx) (ne_of_gt hx)).differentiableWithinAt

/-- `li` is continuous on `(0, 1)`. -/
theorem continuousOn_li_Ioo : ContinuousOn li (Ioo 0 1) :=
  differentiableOn_li_Ioo.continuousOn

/-- `li` is continuous on `(1, ∞)`. -/
theorem continuousOn_li_Ioi : ContinuousOn li (Ioi 1) :=
  differentiableOn_li_Ioi.continuousOn

/-- Closed-form identity for `li` on `(0, 1)` in terms of `log (-log x)` and the Gamma-derivative
kernel `log t * exp (-t)`. -/
theorem li_eq_add_log_neg_log_mul_add_integral {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    li x = eulerMascheroniConstant + log (-log x) * x +
      ∫ t in Ioc 0 (-log x), log t * exp (-t) := by
  set z : ℝ := -log x
  have hz : 0 < z := neg_pos.mpr (log_neg hx0 hx1)
  have hseries : (∑' n : ℕ, log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) =
      -(∫ t in (0 : ℝ)..z, (1 - exp (-t)) / t) := by
    rw [← integral_exp_sub_one_div_eq_tsum (log x)]
    have hsub := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := z)
      (f := fun u : ℝ ↦ (exp u - 1) / u)
    rw [neg_zero, show -z = log x from neg_neg (log x),
      intervalIntegral.integral_symm (0 : ℝ) (log x)] at hsub
    rw [neg_eq_iff_eq_neg.mp hsub.symm]
    congr 1
    exact intervalIntegral.integral_congr fun t _ ↦ by ring
  have hibp := one_sub_exp_neg_mul_log_eq hz.le
  rw [show exp (-z) = x from by rw [show -z = log x from neg_neg _, exp_log hx0]] at hibp
  have hlogz : log (log x) = log z := (log_neg_eq_log (log x)).symm
  rw [li_def, hseries, hlogz]
  change _ = eulerMascheroniConstant + log z * x + ∫ t in Ioc 0 z, log t * exp (-t)
  linarith

/-- `li x → 0` as `x → 0⁺`. -/
theorem tendsto_li_nhdsGT_zero : Tendsto li (𝓝[>] 0) (𝓝 0) := by
  have hz_top : Tendsto (fun x : ℝ ↦ -log x) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp tendsto_log_nhdsGT_zero
  have hterm1 : Tendsto (fun x : ℝ ↦ log (-log x) * x) (𝓝[>] 0) (𝓝 0) := by
    refine (tendsto_log_mul_exp_neg_atTop.comp hz_top).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x (hx0 : 0 < x)
    simp only [Function.comp_def, neg_neg, exp_log hx0]
  have hterm2 : Tendsto (fun z : ℝ ↦ ∫ t in Ioc 0 z, log t * exp (-t)) atTop
      (𝓝 (∫ t in Ioi 0, log t * exp (-t))) := by
    refine (intervalIntegral_tendsto_integral_Ioi (a := (0 : ℝ))
      integrableOn_log_mul_exp_neg_Ioi tendsto_id).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with z hz
    exact intervalIntegral.integral_of_le hz
  have hlim : Tendsto
      (fun x : ℝ ↦ eulerMascheroniConstant + log (-log x) * x +
        ∫ t in Ioc 0 (-log x), log t * exp (-t))
      (𝓝[>] 0) (𝓝 0) := by
    have hsum := ((tendsto_const_nhds (x := eulerMascheroniConstant)).add hterm1).add
      (hterm2.comp hz_top)
    have hzero : eulerMascheroniConstant + 0 +
        ∫ t in Ioi (0 : ℝ), log t * exp (-t) = 0 := by
      rw [eulerMascheroniConstant_eq_neg_integral_log]
      ring
    rwa [hzero] at hsum
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with x ⟨hx0, hx1⟩
  exact (li_eq_add_log_neg_log_mul_add_integral hx0 hx1).symm

/-! ### Antiderivative and offset relation with `Li` -/

/-- **Endpoint-difference formula** on either branch `(0, 1)` or `(1, ∞)` of `li`:
if `a, b > 0` and `1 ∉ uIcc a b`, then `∫ t in a..b, (log t)⁻¹ = li b - li a`. -/
theorem integral_inv_log_eq_li_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h1 : (1 : ℝ) ∉ uIcc a b) :
    (∫ t in a..b, (log t)⁻¹) = li b - li a := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht ↦ ?_)
    (ContinuousOn.intervalIntegrable fun t ht ↦ ?_)
  · exact hasDerivAt_li ((lt_min ha hb).trans_le ht.1) fun h ↦ h1 (h ▸ ht)
  · have ht0 : 0 < t := (lt_min ha hb).trans_le ht.1
    have ht1 : t ≠ 1 := fun h ↦ h1 (h ▸ ht)
    exact ((continuousAt_log ht0.ne').inv₀
      (log_ne_zero_of_pos_of_ne_one ht0 ht1)).continuousWithinAt

/-- On `(1, ∞)`, `li` is an antiderivative of `(log t)⁻¹`:
`∫ t in a..b, (log t)⁻¹ = li b - li a` for `a, b > 1`. -/
theorem integral_inv_log_eq_li_sub_li {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    ∫ t in a..b, (log t)⁻¹ = li b - li a :=
  integral_inv_log_eq_li_sub (zero_lt_one.trans ha) (zero_lt_one.trans hb)
    fun h ↦ by rcases mem_uIcc.mp h with h | h <;> linarith

/-- On `(0, 1)`, `li` is an antiderivative of `(log t)⁻¹`:
`∫ t in a..b, (log t)⁻¹ = li b - li a` for `a, b ∈ (0, 1)`. -/
theorem integral_inv_log_eq_li_sub_li_of_lt_one {a b : ℝ} (ha₀ : 0 < a) (ha : a < 1)
    (hb₀ : 0 < b) (hb : b < 1) :
    ∫ t in a..b, (log t)⁻¹ = li b - li a :=
  integral_inv_log_eq_li_sub ha₀ hb₀ fun h ↦ by rcases mem_uIcc.mp h with h | h <;> linarith

/-- The offset and unoffset logarithmic integrals differ by `li 2` on `(1, ∞)`:
`Li x = li x - li 2`. -/
theorem logIntegral_eq_li_sub_li_two {x : ℝ} (hx : 1 < x) : logIntegral x = li x - li 2 := by
  rw [logIntegral_def, integral_inv_log_eq_li_sub_li one_lt_two hx]

/-- Rearranged offset identity: for every `x > 1`, `li x = Li x + li 2`. -/
theorem li_eq_logIntegral_add_li_two {x : ℝ} (hx : 1 < x) :
    li x = logIntegral x + li 2 := by
  linarith [logIntegral_eq_li_sub_li_two hx]

/-! ### Monotonicity and limits -/

/-- The unoffset logarithmic integral is strictly increasing on `(1, ∞)`. -/
theorem strictMonoOn_li : StrictMonoOn li (Ioi 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 1) continuousOn_li_Ioi fun x hx ↦ ?_
  rw [interior_Ioi] at hx
  rw [deriv_li (zero_lt_one.trans hx) (ne_of_gt hx)]
  exact inv_pos.2 (Real.log_pos hx)

/-- The unoffset logarithmic integral is strictly decreasing on `(0, 1)`. -/
theorem strictAntiOn_li : StrictAntiOn li (Ioo 0 1) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioo 0 1) continuousOn_li_Ioo fun x hx ↦ ?_
  rw [interior_Ioo] at hx
  rw [deriv_li hx.1 (ne_of_lt hx.2)]
  exact inv_lt_zero.2 (Real.log_neg hx.1 hx.2)

/-- `li` is strictly negative on `(0, 1)`. -/
theorem li_neg {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : li x < 0 := by
  have hle : li (x / 2) ≤ 0 := by
    refine le_of_tendsto_of_tendsto tendsto_const_nhds tendsto_li_nhdsGT_zero ?_
    filter_upwards [Ioo_mem_nhdsGT (half_pos hx0)] with y ⟨hy0, hyx⟩
    exact (strictAntiOn_li ⟨hy0, hyx.trans (by linarith)⟩
      ⟨half_pos hx0, by linarith⟩ hyx).le
  exact (strictAntiOn_li ⟨half_pos hx0, by linarith⟩ ⟨hx0, hx1⟩ (by linarith)).trans_le hle

/-- The entire-part series `x ↦ ∑_{n ≥ 1} (log x)^n / (n * n!)` tends to `0` as `x → 1`. -/
theorem tendsto_tsum_log_pow_div_mul_factorial_nhds_one :
    Tendsto (fun x : ℝ ↦ ∑' n : ℕ, log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)))
      (𝓝 1) (𝓝 0) := by
  have hc : ContinuousAt
      (fun t : ℝ ↦ ∑' n : ℕ, log t ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) 1 :=
    continuous_tsum_pow_div_mul_factorial.continuousAt.comp (continuousAt_log one_ne_zero)
  simpa [log_one] using hc.tendsto

/-- The unoffset logarithmic integral tends to `-∞` at `1`, from either side. -/
theorem tendsto_li_nhdsNE_one : Tendsto li (𝓝[≠] 1) atBot := by
  have hlog : Tendsto log (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa using (Real.continuousAt_log one_ne_zero).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [inter_mem_nhdsWithin _ (Ioi_mem_nhds zero_lt_one), self_mem_nhdsWithin]
        with x hx hx1 using Real.log_ne_zero_of_pos_of_ne_one hx.2 hx1
  have hser : Tendsto (fun x ↦ liSeries (log x)) (𝓝[≠] 1) (𝓝 0) := by
    rw [← liSeries_zero]
    exact (continuous_liSeries.tendsto 0).comp (hlog.mono_right nhdsWithin_le_nhds)
  exact ((tendsto_atBot_add_const_left _ eulerMascheroniConstant
    (Real.tendsto_log_nhdsNE_zero.comp hlog)).atBot_add hser).congr
    fun x ↦ (li_eq_add_liSeries x).symm

/-- `li x → -∞` as `x → 1⁺`. -/
theorem tendsto_li_nhdsGT_one : Tendsto li (𝓝[>] 1) atBot :=
  tendsto_li_nhdsNE_one.mono_left (nhdsGT_le_nhdsNE 1)

/-- `li x → -∞` as `x → 1⁻`. -/
theorem tendsto_li_nhdsLT_one : Tendsto li (𝓝[<] 1) atBot :=
  tendsto_li_nhdsNE_one.mono_left (nhdsLT_le_nhdsNE 1)

/-- The unoffset logarithmic integral tends to `+∞` at infinity. -/
theorem tendsto_li_atTop : Tendsto li atTop atTop := by
  have hLi : Tendsto logIntegral atTop atTop :=
    logIntegral_isEquivalent_div_log.tendsto_atTop_iff.mpr tendsto_div_log_atTop
  refine (tendsto_atTop_add_const_right _ (li 2) hLi).congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact (li_eq_logIntegral_add_li_two hx).symm

/-! ### Positivity and Soldner's constant -/

/-- `li (3 / 2) > 0`: with `y = log (3 / 2) > 2 / 5`, the bounds `γ > 1 / 2` and
`liSeries y ≥ y + y² / 4` reduce it to `1 < y e^(1 / 2 + y + y² / 4)`, and
`e^(47 / 50) > 5 / 2` by the first four terms of the exponential series. -/
private theorem li_three_halves_pos : 0 < li (3 / 2) := by
  set y := log (3 / 2) with hy_def
  have hy := Real.two_fifths_lt_log_three_halves
  rw [← hy_def] at hy
  have hy0 : 0 < y := by linarith
  have hs := sum_range_le_liSeries hy0.le 2
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty] at hs
  norm_num [Nat.factorial] at hs
  have he : (5 / 2 : ℝ) < exp (47 / 50) := by
    refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num) 4)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have he' : exp (47 / 50) ≤ exp (1 / 2 + y + y ^ 2 / 4) := Real.exp_le_exp.2 (by nlinarith)
  have hlog : -(1 / 2 + y + y ^ 2 / 4) < log y := by
    rw [Real.lt_log_iff_exp_lt hy0, Real.exp_neg, inv_lt_iff_one_lt_mul₀ (exp_pos _)]
    nlinarith
  rw [li_eq_add_liSeries]
  linarith [Real.one_half_lt_eulerMascheroniConstant]

/-- The unoffset logarithmic integral is positive from `3 / 2` on. -/
theorem li_pos {x : ℝ} (hx : 3 / 2 ≤ x) : 0 < li x := by
  rcases hx.eq_or_lt with rfl | hx
  · exact li_three_halves_pos
  · exact li_three_halves_pos.trans
      (strictMonoOn_li (by norm_num : (1 : ℝ) < 3 / 2) (by simp only [mem_Ioi]; linarith) hx)

/-- `li 2 > 0`. -/
theorem li_two_pos : 0 < li 2 :=
  li_pos (by norm_num)

/-- The unoffset logarithmic integral `li` differs from the offset logarithmic integral `Li`. -/
theorem li_ne_logIntegral : li ≠ logIntegral := by
  intro h
  have h2 := congr_fun h 2
  rw [logIntegral_two] at h2
  linarith [li_two_pos]

/-- Every zero of the unoffset logarithmic integral lies below `3 / 2`. -/
theorem lt_three_halves_of_li_eq_zero {μ : ℝ} (hμ : li μ = 0) : μ < 3 / 2 := by
  by_contra! h
  exact (li_pos h).ne' hμ

/-- **Soldner's constant**: the unoffset logarithmic integral has exactly one zero in `(1, ∞)`. -/
theorem existsUnique_li_eq_zero : ∃! μ, 1 < μ ∧ li μ = 0 := by
  obtain ⟨a, ha, hla⟩ : ∃ a ∈ Ioo (1 : ℝ) (3 / 2), li a < 0 := by
    have h : ∀ᶠ x in 𝓝[>] (1 : ℝ), x ∈ Ioo (1 : ℝ) (3 / 2) ∧ li x < 0 :=
      (eventually_mem_set.2 (Ioo_mem_nhdsGT (by norm_num))).and
        (tendsto_li_nhdsGT_one.eventually (eventually_lt_atBot 0))
    exact h.exists
  have hcont : ContinuousOn li (Icc a (3 / 2)) :=
    continuousOn_li_Ioi.mono fun _ ht ↦ ha.1.trans_le ht.1
  obtain ⟨μ, hμ, hμ0⟩ := intermediate_value_Icc ha.2.le hcont ⟨hla.le, li_three_halves_pos.le⟩
  refine ⟨μ, ⟨ha.1.trans_le hμ.1, hμ0⟩, fun ν hν ↦ ?_⟩
  exact strictMonoOn_li.injOn hν.1 (ha.1.trans_le hμ.1) (hν.2.trans hμ0.symm)

end TauCeti.Real
