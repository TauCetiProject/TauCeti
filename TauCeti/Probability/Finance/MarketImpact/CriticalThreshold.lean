/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.BlackScholes.Greeks
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import TauCeti.Probability.Distributions.Gaussian.Basic
import TauCeti.Probability.Distributions.Gaussian.Cdf
import TauCeti.Probability.Distributions.Gaussian.Smooth

/-!
# Critical thresholds of the call-hedging feedback denominator

When program traders hedge `ρ` Black–Scholes calls by holding `ρ C_x` units of the asset, market
clearing divides the volatility by the clearing derivative

`F(x) = 1 - ρ C_x(x) - x ρ C_xx(x)`

(`TauCeti.Finance.callFeedbackDenominator`). The feedback pricing equation is parabolic only
where `F` is positive. For a call of strike `K > 0` with volatility `σ > 0` and remaining maturity
`τ > 0`, write `s = σ √τ` for the total volatility. Since `C_x = Φ(d₊)` and `x C_xx = φ(d₊) / s`,

`F(x) = 1 - ρ (Φ(d₊) + φ(d₊) / s)`

(`TauCeti.Finance.callFeedbackDenominator_eq`), where `Φ` and `φ` are the standard Gaussian
distribution function and density. As a function of `d = d₊`, the bracket has derivative
`φ(d) (s - d) / s`, so it is largest at `d = s`, where it equals the *call threshold function*

`g(s) = Φ(s) + φ(s) / s`

(`TauCeti.Finance.callThresholdFunction`). The spot with `d₊ = s` is
`x_* = K exp((σ² / 2 - r) τ)`. Hence, for `ρ ≥ 0`, the minimum of `F` over positive spots is
`1 - ρ g(σ √τ)`, attained at `x_*` (`TauCeti.Finance.isMinOn_callFeedbackDenominator`), and
only there when `ρ > 0`
(`TauCeti.Finance.one_sub_mul_callThresholdFunction_lt_callFeedbackDenominator`).

The function `g` decreases strictly on `(0, ∞)`, since `g'(s) = -φ(s) / s²`
(`TauCeti.Finance.hasDerivAt_callThresholdFunction`), from `+∞` at `0⁺` to `1` at `+∞`, so it maps
`(0, ∞)` bijectively onto `(1, ∞)` (`TauCeti.Finance.bijOn_callThresholdFunction`). Consequently:

* for `0 < ρ < 1` there is exactly one *critical total volatility* `s_* > 0` with
  `g(s_*) = 1 / ρ` (`TauCeti.Finance.existsUnique_callThresholdFunction_eq_one_div`), and the
  minimum of `F` is positive, zero or negative according as `τ` is greater than, equal to or less
  than the critical time `s_*² / σ²` (`TauCeti.Finance.one_sub_mul_callThresholdFunction_pos_iff`
  and its two companions);
* for `ρ ≥ 1` the minimum is negative at every positive maturity
  (`TauCeti.Finance.one_sub_mul_callThresholdFunction_neg`);
* as `ρ ↓ 0`, `s_* ∼ ρ / √(2π)`, so the critical time `s_*² / σ²` is asymptotic to
  `ρ² / (2π σ²)` (`TauCeti.Finance.tendsto_div_of_callThresholdFunction_eq_one_div`,
  `TauCeti.Finance.tendsto_sq_div_sq_div_sq_of_callThresholdFunction_eq_one_div`).

For a put the delta is `Φ(d₊) - 1` and the gamma is the call's, so the put denominator has
minimum `1 - ρ (g(σ √τ) - 1)` at the same spot (`TauCeti.Finance.isMinOn_putFeedbackDenominator`),
and its threshold equation `g(s) - 1 = 1 / ρ` has exactly one positive root for every `ρ > 0`
(`TauCeti.Finance.existsUnique_callThresholdFunction_sub_one_eq_one_div`).

A minimum equal to zero puts the denominator of the nonlinear pricing equation exactly at zero, so
an existence theory for that equation has to start from a maturity strictly beyond the critical
time, where the minimum is a strictly positive margin.

## References

* R. Sircar, G. Papanicolaou, *General Black–Scholes models accounting for increased market
  volatility from hedging strategies*, Applied Mathematical Finance 5 (1998), 45–82, §2.7.1.
-/

public section

noncomputable section

open Filter ProbabilityTheory Real Set TauCeti.BlackScholes TauCeti.Probability
open scoped Topology

namespace TauCeti.Finance

variable {ρ r σ K τ x s : ℝ}

/-! ### The call threshold function -/

/-- The *call threshold function* `g(s) = Φ(s) + φ(s) / s`, where `Φ` and `φ` are the standard
Gaussian distribution function and density. At total volatility `s = σ √τ > 0` it is the largest
value of the call delta plus spot times gamma, `C_x + x C_xx`, over positive spots. At `s = 0`
Lean's division convention gives the value `1 / 2`, whereas the right limit is `+∞`. -/
def callThresholdFunction (s : ℝ) : ℝ :=
  cdf (gaussianReal 0 1) s + gaussianPDFReal 0 1 s / s

/-- Unfold the call threshold function. -/
theorem callThresholdFunction_def (s : ℝ) :
    callThresholdFunction s = cdf (gaussianReal 0 1) s + gaussianPDFReal 0 1 s / s :=
  (rfl)

/-- The derivative of `d ↦ Φ(d) + φ(d) / s` is `φ(d) (s - d) / s`. -/
private theorem hasDerivAt_cdf_add_gaussianPDFReal_div (hs : s ≠ 0) (d : ℝ) :
    HasDerivAt (fun d => cdf (gaussianReal 0 1) d + gaussianPDFReal 0 1 d / s)
      (gaussianPDFReal 0 1 d * (s - d) / s) d := by
  convert (hasDerivAt_cdf_gaussianReal 0 one_ne_zero d).add
    ((hasDerivAt_gaussianPDFReal 0 1 d).div_const s) using 1
  simp only [sub_zero, NNReal.coe_one, div_one]
  field_simp
  ring

/-- **The derivative of the call threshold function** is `g'(s) = -φ(s) / s²` for `s ≠ 0`. -/
theorem hasDerivAt_callThresholdFunction (hs : s ≠ 0) :
    HasDerivAt callThresholdFunction (-(gaussianPDFReal 0 1 s / s ^ 2)) s := by
  have h := (hasDerivAt_cdf_gaussianReal 0 one_ne_zero s).add
    ((hasDerivAt_gaussianPDFReal 0 1 s).div (hasDerivAt_id s) hs)
  convert h using 1
  · ext u
    simp [callThresholdFunction_def]
  · simp only [id_eq, sub_zero, NNReal.coe_one, div_one]
    field_simp
    ring

/-- The call threshold function is continuous on `(0, ∞)`. -/
theorem continuousOn_callThresholdFunction : ContinuousOn callThresholdFunction (Ioi 0) :=
  fun _ hs => (hasDerivAt_callThresholdFunction (ne_of_gt hs)).continuousAt.continuousWithinAt

/-- The call threshold function is strictly decreasing on `(0, ∞)`. -/
theorem strictAntiOn_callThresholdFunction : StrictAntiOn callThresholdFunction (Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0) continuousOn_callThresholdFunction
    fun s hs => ?_
  rw [interior_Ioi] at hs
  rw [(hasDerivAt_callThresholdFunction (ne_of_gt hs)).deriv, neg_neg_iff_pos]
  have := gaussianPDFReal_pos 0 1 s one_ne_zero
  have : 0 < s ^ 2 := pow_pos hs 2
  positivity

/-- The call threshold function tends to `1` at `+∞`. -/
theorem tendsto_callThresholdFunction_atTop :
    Tendsto callThresholdFunction atTop (𝓝 1) := by
  have hφ := ((tendsto_gaussianPDFReal_cocompact 0 1).mono_left atTop_le_cocompact).mul
    tendsto_inv_atTop_zero
  have h := (tendsto_cdf_atTop (gaussianReal 0 1)).add hφ
  rw [mul_zero, add_zero] at h
  exact h.congr fun s => by rw [callThresholdFunction_def, div_eq_mul_inv]

/-- Near zero, `s g(s) = s Φ(s) + φ(s)` tends to `φ(0) = 1 / √(2π)`. -/
theorem tendsto_mul_callThresholdFunction_nhdsGT_zero :
    Tendsto (fun s => s * callThresholdFunction s) (𝓝[>] 0) (𝓝 (√(2 * π))⁻¹) := by
  have hΦ : Continuous (cdf (gaussianReal 0 1)) :=
    (contDiff_cdf_gaussianReal 0 (n := 0) one_ne_zero).continuous
  have hφ : Continuous (gaussianPDFReal 0 1) := (contDiff_gaussianPDFReal 0 1 (n := 0)).continuous
  have h : Tendsto (fun s => s * cdf (gaussianReal 0 1) s + gaussianPDFReal 0 1 s) (𝓝 0)
      (𝓝 (0 * cdf (gaussianReal 0 1) 0 + gaussianPDFReal 0 1 0)) :=
    ((continuous_id.mul hΦ).add hφ).tendsto 0
  rw [zero_mul, zero_add, gaussianPDFReal_self, NNReal.coe_one, mul_one] at h
  refine (h.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [callThresholdFunction_def, mul_add, mul_div_cancel₀ _ (ne_of_gt hs)]

/-- The call threshold function tends to `+∞` at `0⁺`. -/
theorem tendsto_callThresholdFunction_nhdsGT_zero :
    Tendsto callThresholdFunction (𝓝[>] 0) atTop := by
  have h := tendsto_mul_callThresholdFunction_nhdsGT_zero.pos_mul_atTop
    (by positivity) tendsto_inv_nhdsGT_zero
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [mul_comm s, mul_assoc, mul_inv_cancel₀ (ne_of_gt hs), mul_one]

/-- The call threshold function exceeds `1` on `(0, ∞)`: this is Mills' ratio bound
`1 - Φ(s) < φ(s)/s` rearranged. -/
theorem one_lt_callThresholdFunction (hs : 0 < s) : 1 < callThresholdFunction s := by
  have := one_sub_cdf_gaussianReal_lt_gaussianPDFReal_div hs
  rw [callThresholdFunction_def]
  linarith

/-- The call threshold function maps `(0, ∞)` bijectively onto `(1, ∞)`. -/
theorem bijOn_callThresholdFunction : BijOn callThresholdFunction (Ioi 0) (Ioi 1) := by
  refine ⟨fun s hs => one_lt_callThresholdFunction hs, strictAntiOn_callThresholdFunction.injOn,
    fun c hc => ?_⟩
  -- Find `0 < a ≤ b` with `g b ≤ c ≤ g a` and apply the intermediate value theorem on `[a, b]`.
  obtain ⟨a, ha, hac⟩ :=
    ((tendsto_callThresholdFunction_nhdsGT_zero.eventually_ge_atTop c).and
      self_mem_nhdsWithin).exists
  obtain ⟨b, hbc, hab⟩ := ((tendsto_order.1 tendsto_callThresholdFunction_atTop).2 c hc |>.and
    (eventually_ge_atTop a)).exists
  have hcont : ContinuousOn callThresholdFunction (Icc a b) :=
    continuousOn_callThresholdFunction.mono fun u hu => lt_of_lt_of_le hac hu.1
  obtain ⟨u, hu, rfl⟩ := intermediate_value_Icc' hab hcont ⟨hbc.le, ha⟩
  exact ⟨u, lt_of_lt_of_le hac hu.1, rfl⟩

/-- Above `1`, every value of the call threshold function is taken at exactly one positive total
volatility. -/
theorem existsUnique_callThresholdFunction_eq {c : ℝ} (hc : 1 < c) :
    ∃! s, 0 < s ∧ callThresholdFunction s = c := by
  obtain ⟨s, hs, rfl⟩ := bijOn_callThresholdFunction.surjOn hc
  exact ⟨s, ⟨hs, rfl⟩, fun u hu => bijOn_callThresholdFunction.injOn hu.1 hs hu.2⟩

/-- **The critical call threshold.** For feedback `0 < ρ < 1` there is exactly one critical total
volatility `s > 0` with `g(s) = 1 / ρ`. -/
theorem existsUnique_callThresholdFunction_eq_one_div (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) :
    ∃! s, 0 < s ∧ callThresholdFunction s = 1 / ρ :=
  existsUnique_callThresholdFunction_eq ((one_lt_div hρ₀).2 hρ₁)

/-- **The critical put threshold.** For every feedback `ρ > 0` there is exactly one total
volatility `s > 0` with `g(s) - 1 = 1 / ρ`. -/
theorem existsUnique_callThresholdFunction_sub_one_eq_one_div (hρ : 0 < ρ) :
    ∃! s, 0 < s ∧ callThresholdFunction s - 1 = 1 / ρ := by
  simpa only [sub_eq_iff_eq_add'] using
    existsUnique_callThresholdFunction_eq (c := 1 + 1 / ρ) (by simp [hρ])

/-! ### Maximizing `Φ(d) + φ(d) / s` over `d` -/

/-- For `s > 0`, `Φ(d) + φ(d) / s` is strictly less than `g(s)`, its value at `d = s`, for every
`d ≠ s`. -/
theorem cdf_add_gaussianPDFReal_div_lt_callThresholdFunction {d : ℝ} (hs : 0 < s) (hd : d ≠ s) :
    cdf (gaussianReal 0 1) d + gaussianPDFReal 0 1 d / s < callThresholdFunction s := by
  rw [callThresholdFunction_def]
  set m := fun d => cdf (gaussianReal 0 1) d + gaussianPDFReal 0 1 d / s
  have hm : ∀ d, HasDerivAt m (gaussianPDFReal 0 1 d * (s - d) / s) d :=
    hasDerivAt_cdf_add_gaussianPDFReal_div (ne_of_gt hs)
  have hcont : Continuous m := continuous_iff_continuousAt.2 fun d => (hm d).continuousAt
  have hφ := fun d => gaussianPDFReal_pos 0 1 d one_ne_zero
  -- `m` increases on `(-∞, s]` and decreases on `[s, ∞)`, so `m d < m s`.
  rcases lt_or_gt_of_ne hd with hd | hd
  · refine strictMonoOn_of_deriv_pos (convex_Iic s) hcont.continuousOn (fun u hu => ?_)
      (mem_Iic.2 hd.le) self_mem_Iic hd
    rw [interior_Iic, mem_Iio] at hu
    rw [(hm u).deriv]
    have := hφ u
    have : 0 < s - u := sub_pos.2 hu
    positivity
  · refine strictAntiOn_of_deriv_neg (convex_Ici s) hcont.continuousOn (fun u hu => ?_)
      self_mem_Ici (mem_Ici.2 hd.le) hd
    rw [interior_Ici, mem_Ioi] at hu
    rw [(hm u).deriv]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (hφ u) (sub_neg.2 hu)) hs

/-- For `s > 0`, `Φ(d) + φ(d) / s` is at most `g(s)`, its value at `d = s`. -/
theorem cdf_add_gaussianPDFReal_div_le_callThresholdFunction (hs : 0 < s) (d : ℝ) :
    cdf (gaussianReal 0 1) d + gaussianPDFReal 0 1 d / s ≤ callThresholdFunction s := by
  rcases eq_or_ne d s with rfl | hd
  · exact le_rfl
  · exact (cdf_add_gaussianPDFReal_div_lt_callThresholdFunction hs hd).le

/-! ### The sign of the minimum and the critical time -/

/-- A critical total volatility `s > 0`, with `g(s) = 1 / ρ`, forces `ρ > 0`. -/
private theorem pos_of_callThresholdFunction_eq_one_div (hs : 0 < s)
    (hroot : callThresholdFunction s = 1 / ρ) : 0 < ρ :=
  one_div_pos.1 (hroot ▸ one_pos.trans (one_lt_callThresholdFunction hs))

/-- Below a critical total volatility `s > 0`, with `g(s) = 1 / ρ`, `1 - ρ g` is negative, and
only there. -/
private theorem one_sub_mul_callThresholdFunction_neg_iff_lt {u : ℝ} (hs : 0 < s)
    (hroot : callThresholdFunction s = 1 / ρ) (hu : 0 < u) :
    1 - ρ * callThresholdFunction u < 0 ↔ u < s := by
  have hρ := pos_of_callThresholdFunction_eq_one_div hs hroot
  rw [sub_neg, ← div_lt_iff₀' hρ, ← hroot]
  exact strictAntiOn_callThresholdFunction.lt_iff_gt hs hu

/-- Above a critical total volatility `s > 0`, with `g(s) = 1 / ρ`, `1 - ρ g` is positive, and
only there. -/
private theorem one_sub_mul_callThresholdFunction_pos_iff_lt {u : ℝ} (hs : 0 < s)
    (hroot : callThresholdFunction s = 1 / ρ) (hu : 0 < u) :
    0 < 1 - ρ * callThresholdFunction u ↔ s < u := by
  have hρ := pos_of_callThresholdFunction_eq_one_div hs hroot
  rw [sub_pos, ← lt_div_iff₀' hρ, ← hroot]
  exact strictAntiOn_callThresholdFunction.lt_iff_gt hu hs

/-- **Positive minimum beyond the critical time.** Let `s > 0` be a critical total volatility,
`g(s) = 1 / ρ`. For `σ > 0` and remaining maturity `τ > 0`, the minimum `1 - ρ g(σ √τ)` of the
call feedback denominator is positive exactly when `τ` exceeds the critical time `s² / σ²`. -/
theorem one_sub_mul_callThresholdFunction_pos_iff (hs : 0 < s)
    (hroot : callThresholdFunction s = 1 / ρ) (hσ : 0 < σ) (hτ : 0 < τ) :
    0 < 1 - ρ * callThresholdFunction (σ * √τ) ↔ s ^ 2 / σ ^ 2 < τ := by
  rw [one_sub_mul_callThresholdFunction_pos_iff_lt hs hroot (by positivity), ← div_lt_iff₀' hσ,
    lt_sqrt (by positivity), div_pow]

/-- **Negative minimum before the critical time.** Let `s > 0` be a critical total volatility,
`g(s) = 1 / ρ`. For `σ > 0` and remaining maturity `τ > 0`, the minimum `1 - ρ g(σ √τ)` of the
call feedback denominator is negative exactly when `τ` is less than the critical time
`s² / σ²`. -/
theorem one_sub_mul_callThresholdFunction_neg_iff (hs : 0 < s)
    (hroot : callThresholdFunction s = 1 / ρ) (hσ : 0 < σ) (hτ : 0 < τ) :
    1 - ρ * callThresholdFunction (σ * √τ) < 0 ↔ τ < s ^ 2 / σ ^ 2 := by
  rw [one_sub_mul_callThresholdFunction_neg_iff_lt hs hroot (by positivity), ← lt_div_iff₀' hσ,
    sqrt_lt' (by positivity), div_pow]

/-- **Zero minimum at the critical time.** Let `s > 0` be a critical total volatility,
`g(s) = 1 / ρ`. For `σ > 0` and remaining maturity `τ > 0`, the minimum `1 - ρ g(σ √τ)` of the
call feedback denominator vanishes exactly at the critical time `τ = s² / σ²`. -/
theorem one_sub_mul_callThresholdFunction_eq_zero_iff (hs : 0 < s)
    (hroot : callThresholdFunction s = 1 / ρ) (hσ : 0 < σ) (hτ : 0 < τ) :
    1 - ρ * callThresholdFunction (σ * √τ) = 0 ↔ τ = s ^ 2 / σ ^ 2 := by
  have hpos := one_sub_mul_callThresholdFunction_pos_iff hs hroot hσ hτ
  have hneg := one_sub_mul_callThresholdFunction_neg_iff hs hroot hσ hτ
  constructor
  · intro h
    exact le_antisymm (not_lt.1 fun h' => (hpos.2 h').ne' h) (not_lt.1 fun h' => (hneg.2 h').ne h)
  · intro h
    exact le_antisymm (not_lt.1 fun h' => (hpos.1 h').ne h.symm)
      (not_lt.1 fun h' => (hneg.1 h').ne h)

/-- **No positive margin for feedback `ρ ≥ 1`.** At every positive total volatility `s`,
`1 - ρ g(s)` is negative. -/
theorem one_sub_mul_callThresholdFunction_neg (hρ : 1 ≤ ρ) (hs : 0 < s) :
    1 - ρ * callThresholdFunction s < 0 := by
  have := one_lt_callThresholdFunction hs
  nlinarith

/-- **Small-feedback asymptotics of the critical total volatility.** If `s(ρ) > 0` solves
`g(s(ρ)) = 1 / ρ` for all small `ρ > 0`, then `s(ρ) / ρ → 1 / √(2π)` as `ρ ↓ 0`. -/
theorem tendsto_div_of_callThresholdFunction_eq_one_div {s : ℝ → ℝ}
    (hs : ∀ᶠ ρ in 𝓝[>] 0, 0 < s ρ ∧ callThresholdFunction (s ρ) = 1 / ρ) :
    Tendsto (fun ρ => s ρ / ρ) (𝓝[>] 0) (𝓝 (√(2 * π))⁻¹) := by
  -- First, `s(ρ) → 0⁺`: if `s(ρ) ≥ a > 0` then `1 / ρ = g(s(ρ)) ≤ g(a)`, so `ρ ≥ 1 / g(a)`.
  have h0 : Tendsto s (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_order.2 ⟨fun a ha => hs.mono fun ρ h => ha.trans h.1,
      fun a ha => ?_⟩, hs.mono fun ρ h => h.1⟩
    have hga : 0 < callThresholdFunction a := one_pos.trans (one_lt_callThresholdFunction ha)
    have hρa : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ < 1 / callThresholdFunction a :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by positivity))
    filter_upwards [hs, hρa, self_mem_nhdsWithin] with ρ ⟨hpos, hroot⟩ hρa hρ
    by_contra hle
    have hg := strictAntiOn_callThresholdFunction.antitoneOn ha hpos (not_lt.1 hle)
    rw [hroot] at hg
    exact (lt_one_div hga hρ).2 hρa |>.not_ge hg
  -- Then `s(ρ) / ρ = s(ρ) g(s(ρ))`, and `u g(u) → 1 / √(2π)` as `u ↓ 0`.
  refine (tendsto_mul_callThresholdFunction_nhdsGT_zero.comp h0).congr' ?_
  filter_upwards [hs] with ρ ⟨_, hroot⟩
  rw [Function.comp_apply, hroot, mul_one_div]

/-- **Small-feedback asymptotics of the critical time.** If `s(ρ) > 0` solves `g(s(ρ)) = 1 / ρ` for
all small `ρ > 0`, then the critical time `s(ρ)² / σ²` is asymptotic to `ρ² / (2π σ²)` as `ρ ↓ 0`
(for `σ = 0` both sides vanish under Lean's division convention). -/
theorem tendsto_sq_div_sq_div_sq_of_callThresholdFunction_eq_one_div {s : ℝ → ℝ} (σ : ℝ)
    (hs : ∀ᶠ ρ in 𝓝[>] 0, 0 < s ρ ∧ callThresholdFunction (s ρ) = 1 / ρ) :
    Tendsto (fun ρ => s ρ ^ 2 / σ ^ 2 / ρ ^ 2) (𝓝[>] 0) (𝓝 (2 * π * σ ^ 2)⁻¹) := by
  have h := ((tendsto_div_of_callThresholdFunction_eq_one_div hs).pow 2).div_const (σ ^ 2)
  rw [inv_pow, sq_sqrt (by positivity)] at h
  convert h using 2 with ρ
  · ring
  · rw [mul_inv, div_eq_mul_inv]

/-! ### The feedback denominators of a hedged call and put -/

/-- The *call feedback denominator* `1 - ρ C_x - x (ρ C_xx)` at spot `x`, for program traders
holding the delta of `ρ` Black–Scholes calls of strike `K` and remaining maturity `τ`. It is the
clearing derivative `1 - h - x k` of `TauCeti.Finance.FeedbackParabolicMargins` for demand level
`h = ρ C_x` and demand slope `k = ρ C_xx`, the denominator of the feedback volatility. -/
def callFeedbackDenominator (ρ r σ K τ x : ℝ) : ℝ :=
  1 - ρ * deriv (fun y => callPrice y r σ K τ) x -
    x * (ρ * deriv (deriv fun y => callPrice y r σ K τ) x)

/-- Unfold the call feedback denominator. -/
theorem callFeedbackDenominator_def (ρ r σ K τ x : ℝ) :
    callFeedbackDenominator ρ r σ K τ x = 1 - ρ * deriv (fun y => callPrice y r σ K τ) x -
      x * (ρ * deriv (deriv fun y => callPrice y r σ K τ) x) :=
  (rfl)

/-- Without program trading the call feedback denominator is `1`. -/
@[simp]
theorem callFeedbackDenominator_zero_left (r σ K τ x : ℝ) :
    callFeedbackDenominator 0 r σ K τ x = 1 := by
  simp [callFeedbackDenominator_def]

/-- In terms of `d₊`, the call feedback denominator is `1 - ρ (Φ(d₊) + φ(d₊) / (σ √τ))`. -/
theorem callFeedbackDenominator_eq (hx : 0 < x) (hK : 0 < K) (hσ : σ ≠ 0) (hτ : 0 < τ) :
    callFeedbackDenominator ρ r σ K τ x = 1 - ρ * (cdf (gaussianReal 0 1) (dPlus x r σ K τ) +
      gaussianPDFReal 0 1 (dPlus x r σ K τ) / (σ * √τ)) := by
  rw [callFeedbackDenominator_def, deriv_callPrice_spot hx hK hσ hτ,
    (hasDerivAt_deriv_callPrice_spot hx hK hσ hτ).deriv]
  field_simp
  ring

/-- At the spot `K exp((σ² / 2 - r) τ)` the call feedback denominator equals `1 - ρ g(σ √τ)`. -/
theorem callFeedbackDenominator_mul_exp (hK : 0 < K) (hσ : σ ≠ 0) (hτ : 0 < τ) :
    callFeedbackDenominator ρ r σ K τ (K * exp ((σ ^ 2 / 2 - r) * τ)) =
      1 - ρ * callThresholdFunction (σ * √τ) := by
  rw [callFeedbackDenominator_eq (by positivity) hK hσ hτ,
    (dPlus_eq_mul_sqrt_iff (by positivity) hK (mul_ne_zero hσ (sqrt_ne_zero'.2 hτ))).2 rfl,
    callThresholdFunction_def]

/-- **The minimum of the call feedback denominator.** For feedback `ρ ≥ 0`, the call feedback
denominator is at least `1 - ρ g(σ √τ)` at every positive spot. -/
theorem one_sub_mul_callThresholdFunction_le_callFeedbackDenominator (hρ : 0 ≤ ρ) (hx : 0 < x)
    (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ) :
    1 - ρ * callThresholdFunction (σ * √τ) ≤ callFeedbackDenominator ρ r σ K τ x := by
  rw [callFeedbackDenominator_eq hx hK hσ.ne' hτ]
  gcongr
  exact cdf_add_gaussianPDFReal_div_le_callThresholdFunction (by positivity) _

/-- **The minimizing spot.** For feedback `ρ ≥ 0`, the call feedback denominator attains its
minimum over positive spots at `K exp((σ² / 2 - r) τ)`. -/
theorem isMinOn_callFeedbackDenominator (hρ : 0 ≤ ρ) (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ) :
    IsMinOn (callFeedbackDenominator ρ r σ K τ) (Ioi 0) (K * exp ((σ ^ 2 / 2 - r) * τ)) :=
  isMinOn_iff.2 fun x hx => by
    rw [callFeedbackDenominator_mul_exp hK hσ.ne' hτ]
    exact one_sub_mul_callThresholdFunction_le_callFeedbackDenominator hρ hx hK hσ hτ

/-- **The minimizing spot is unique.** For feedback `ρ > 0`, the call feedback denominator exceeds
its minimum `1 - ρ g(σ √τ)` at every positive spot other than `K exp((σ² / 2 - r) τ)`. -/
theorem one_sub_mul_callThresholdFunction_lt_callFeedbackDenominator (hρ : 0 < ρ) (hx : 0 < x)
    (hxK : x ≠ K * exp ((σ ^ 2 / 2 - r) * τ)) (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ) :
    1 - ρ * callThresholdFunction (σ * √τ) < callFeedbackDenominator ρ r σ K τ x := by
  rw [callFeedbackDenominator_eq hx hK hσ.ne' hτ]
  gcongr
  exact cdf_add_gaussianPDFReal_div_lt_callThresholdFunction (by positivity)
    fun h => hxK ((dPlus_eq_mul_sqrt_iff hx hK (by positivity)).1 h)

/-- The *put feedback denominator* `1 - ρ P_x - x (ρ P_xx)` at spot `x`, for program traders
holding the delta of `ρ` Black–Scholes puts of strike `K` and remaining maturity `τ`. -/
def putFeedbackDenominator (ρ r σ K τ x : ℝ) : ℝ :=
  1 - ρ * deriv (fun y => putPrice y r σ K τ) x -
    x * (ρ * deriv (deriv fun y => putPrice y r σ K τ) x)

/-- Unfold the put feedback denominator. -/
theorem putFeedbackDenominator_def (ρ r σ K τ x : ℝ) :
    putFeedbackDenominator ρ r σ K τ x = 1 - ρ * deriv (fun y => putPrice y r σ K τ) x -
      x * (ρ * deriv (deriv fun y => putPrice y r σ K τ) x) :=
  (rfl)

/-- Without program trading the put feedback denominator is `1`. -/
@[simp]
theorem putFeedbackDenominator_zero_left (r σ K τ x : ℝ) :
    putFeedbackDenominator 0 r σ K τ x = 1 := by
  simp [putFeedbackDenominator_def]

/-- The put delta is the call delta minus one and the gammas agree, so the put feedback
denominator is the call feedback denominator plus `ρ`. -/
theorem putFeedbackDenominator_eq_callFeedbackDenominator_add (hx : 0 < x) (hK : 0 < K)
    (hσ : σ ≠ 0) (hτ : 0 < τ) :
    putFeedbackDenominator ρ r σ K τ x = callFeedbackDenominator ρ r σ K τ x + ρ := by
  rw [putFeedbackDenominator_def, callFeedbackDenominator_def, deriv_putPrice_spot hx hK hσ hτ,
    deriv_deriv_putPrice_spot hx hK hσ hτ, deriv_callPrice_spot hx hK hσ hτ,
    cdf_gaussianReal_zero_one_neg]
  ring

/-- **The minimum of the put feedback denominator.** For feedback `ρ ≥ 0`, the put feedback
denominator attains its minimum over positive spots, `1 - ρ (g(σ √τ) - 1)`, at
`K exp((σ² / 2 - r) τ)`. -/
theorem isMinOn_putFeedbackDenominator (hρ : 0 ≤ ρ) (hK : 0 < K) (hσ : 0 < σ) (hτ : 0 < τ) :
    IsMinOn (putFeedbackDenominator ρ r σ K τ) (Ioi 0) (K * exp ((σ ^ 2 / 2 - r) * τ)) :=
  isMinOn_iff.2 fun x hx => by
    rw [putFeedbackDenominator_eq_callFeedbackDenominator_add (by positivity) hK hσ.ne' hτ,
      putFeedbackDenominator_eq_callFeedbackDenominator_add hx hK hσ.ne' hτ]
    linarith [isMinOn_iff.1 (isMinOn_callFeedbackDenominator (r := r) hρ hK hσ hτ) x hx]

/-- At the spot `K exp((σ² / 2 - r) τ)` the put feedback denominator equals
`1 - ρ (g(σ √τ) - 1)`. -/
theorem putFeedbackDenominator_mul_exp (hK : 0 < K) (hσ : σ ≠ 0) (hτ : 0 < τ) :
    putFeedbackDenominator ρ r σ K τ (K * exp ((σ ^ 2 / 2 - r) * τ)) =
      1 - ρ * (callThresholdFunction (σ * √τ) - 1) := by
  rw [putFeedbackDenominator_eq_callFeedbackDenominator_add (by positivity) hK hσ hτ,
    callFeedbackDenominator_mul_exp hK hσ hτ]
  ring

end TauCeti.Finance
