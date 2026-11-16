/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import TauCeti.Analysis.SpecialFunctions.LogIntegral.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
# The unoffset logarithmic integral

This file defines the unoffset (principal-value) logarithmic integral
`li x = γ + log |log x| + ∑_{n ≥ 1} (log x) ^ n / (n · n!)` as
`TauCeti.Real.principalLogIntegral`, develops its basic calculus and limiting behaviour on
`(0, 1) ∪ (1, ∞)`, and relates it to the offset logarithmic integral
`Li x = TauCeti.Real.logIntegral x = ∫₂ˣ dt / log t`.

Because `(log t)⁻¹` has a nonintegrable singularity at `t = 1`, defining `li` via the
exponential-integral series avoids junk values from Lebesgue integration across the pole; the
ordinary integral on `(0, 1)`, the Cauchy principal value on `(1, ∞)`, and the offset identity
`Li x = li x - li 2` are then proved as theorems.

## Main declarations

* `TauCeti.Real.principalLogIntegral` — the unoffset logarithmic integral `li x`.
* `TauCeti.Real.summable_pow_div_mul_factorial`,
  `TauCeti.Real.hasDerivAt_tsum_pow_div_mul_factorial`,
  `TauCeti.Real.integral_exp_sub_one_div_eq_tsum` — power-series calculus for
  `∑_{n ≥ 1} y ^ n / (n · n!)`.
* `TauCeti.Real.hasDerivAt_principalLogIntegral` — `li' x = (log x)⁻¹` for `0 < x`, `x ≠ 1`.
* `TauCeti.Real.eulerMascheroniConstant_eq_integral_sub_integral` —
  `γ = ∫₀¹ (1 - e^{-t}) / t dt - ∫₁^∞ e^{-t} / t dt`.
* `TauCeti.Real.tendsto_principalLogIntegral_nhdsGT_zero` — `li x → 0` as `x → 0⁺`.
* `TauCeti.Real.principalLogIntegral_eq_integral` — `li x = ∫₀ˣ dt / log t` for `0 < x < 1`.
* `TauCeti.Real.tendsto_principalLogIntegral_pv` — Cauchy principal value of `∫₀ˣ dt / log t` for
  `1 < x`.
* `TauCeti.Real.logIntegral_eq_principalLogIntegral_sub` — `Li x = li x - li 2` for `1 < x`.
* `TauCeti.Real.strictAntiOn_principalLogIntegral`,
  `TauCeti.Real.strictMonoOn_principalLogIntegral`,
  `TauCeti.Real.existsUnique_principalLogIntegral_eq_zero` — monotonicity, sign, and unique zero
  in `(1, ∞)` (Soldner's constant).

## References

* NIST Digital Library of Mathematical Functions (DLMF), §6.2 (Exponential and Logarithmic
  Integrals).
* L. Schoenfeld, *Sharper bounds for the Chebyshev functions `θ(x)` and `ψ(x)`. II*,
  Math. Comp. 30 (1976), 337–360.
-/

public section

namespace TauCeti.Real

open Filter MeasureTheory Set
open scoped Topology Nat

/-! ### Definition and power-series calculus -/

/-- The **unoffset (principal-value) logarithmic integral**
`li x = γ + log |log x| + ∑_{n ≥ 1} (log x) ^ n / (n · n!)`.

In Mathlib `Real.log` satisfies `Real.log (-u) = Real.log u`, so `Real.log (Real.log x)` equals
`Real.log |Real.log x|` for all `x > 0`, `x ≠ 1`. At `x = 1` the value is junk (`γ`). For
`0 < x < 1` this agrees with `∫₀ˣ (log t)⁻¹ dt`, and for `x > 1` it is the Cauchy principal value
of `∫₀ˣ (log t)⁻¹ dt` and satisfies `Li x = li x - li 2`. -/
noncomputable def principalLogIntegral (x : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (Real.log x) +
    ∑' n : ℕ, Real.log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))

/-- Defining equation of `TauCeti.Real.principalLogIntegral`. -/
theorem principalLogIntegral_def (x : ℝ) :
    principalLogIntegral x =
      Real.eulerMascheroniConstant + Real.log (Real.log x) +
        ∑' n : ℕ, Real.log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := (rfl)

/-- The exponential-integral power series `∑_{n ≥ 1} y ^ n / (n · n!)` converges absolutely for
every real `y`. -/
theorem summable_pow_div_mul_factorial (y : ℝ) :
    Summable fun n : ℕ ↦ y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
  have hmaj : Summable fun n : ℕ ↦ |y| ^ (n + 1) / ((n + 1)! : ℝ) :=
    (Real.summable_pow_div_factorial |y|).comp_injective Nat.succ_injective
  refine hmaj.of_norm_bounded fun n ↦ ?_
  rw [Real.norm_eq_abs, abs_div, abs_pow,
    abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1) * (n + 1)!)]
  exact div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg y) _) (by positivity)
    (le_mul_of_one_le_left (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) n]))

/-- The shifted exponential series `∑_{n ≥ 0} y ^ n / (n + 1)!` equals `(exp y - 1) / y` for
`y ≠ 0` and `1` at `y = 0`. -/
theorem tsum_pow_div_factorial_succ (y : ℝ) :
    (∑' n : ℕ, y ^ n / ((n + 1)! : ℝ)) = if y = 0 then 1 else (Real.exp y - 1) / y := by
  split_ifs with hy
  · subst hy
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      simp [zero_pow hn]
  · have hsum : Summable fun n : ℕ ↦ y ^ n / ((n + 1)! : ℝ) := by
      have h1 : Summable fun n : ℕ ↦ y ^ (n + 1) / ((n + 1)! : ℝ) :=
        (Real.summable_pow_div_factorial y).comp_injective Nat.succ_injective
      simpa [pow_succ', mul_div_assoc, hy] using h1.mul_left y⁻¹
    have hexp : Real.exp y = ∑' n : ℕ, y ^ n / (n ! : ℝ) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    have hsplit : Real.exp y = 1 + ∑' n : ℕ, y ^ (n + 1) / ((n + 1)! : ℝ) := by
      rw [hexp, (Real.summable_pow_div_factorial y).tsum_eq_zero_add]
      simp
    have hmul : y * ∑' n : ℕ, y ^ n / ((n + 1)! : ℝ) = Real.exp y - 1 := by
      rw [← hsum.tsum_mul_left]
      have hcongr : (fun n : ℕ ↦ y * (y ^ n / ((n + 1)! : ℝ))) =
          fun n : ℕ ↦ y ^ (n + 1) / ((n + 1)! : ℝ) := by
        ext n
        rw [pow_succ', mul_div_assoc]
      rw [hcongr]
      linarith
    exact (eq_div_iff hy).mpr (by linarith)

/-- Termwise differentiation of the exponential-integral series `∑_{n ≥ 1} y ^ n / (n · n!)`. -/
theorem hasDerivAt_tsum_pow_div_mul_factorial (y : ℝ) :
    HasDerivAt (fun t : ℝ ↦ ∑' n : ℕ, t ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)))
      (if y = 0 then 1 else (Real.exp y - 1) / y) y := by
  set R : ℝ := |y| + 1
  have hR : 0 < R := by positivity
  have hu : Summable fun n : ℕ ↦ R ^ n / ((n + 1)! : ℝ) := by
    have h1 : Summable fun n : ℕ ↦ R ^ (n + 1) / ((n + 1)! : ℝ) :=
      (Real.summable_pow_div_factorial R).comp_injective Nat.succ_injective
    simpa [pow_succ', mul_div_assoc, hR.ne'] using h1.mul_left R⁻¹
  have hg : ∀ (n : ℕ) (t : ℝ), t ∈ Ioo (-R) R →
      HasDerivAt (fun z : ℝ ↦ z ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)))
        (t ^ n / ((n + 1)! : ℝ)) t := by
    intro n t _
    have h1 := (hasDerivAt_pow (n + 1) t).div_const (((n : ℝ) + 1) * ((n + 1)! : ℝ))
    refine h1.congr_deriv ?_
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp [hn1]
  have hg' : ∀ (n : ℕ) (t : ℝ), t ∈ Ioo (-R) R →
      ‖t ^ n / ((n + 1)! : ℝ)‖ ≤ R ^ n / ((n + 1)! : ℝ) := by
    intro n t ht
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < (n + 1)!)]
    gcongr
    exact (abs_lt.mpr ht).le
  have hd := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo hg hg'
    (⟨by linarith, hR⟩ : (0 : ℝ) ∈ Ioo (-R) R) (summable_pow_div_mul_factorial 0)
    (⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩ : y ∈ Ioo (-R) R)
  rwa [tsum_pow_div_factorial_succ] at hd

/-- The exponential-integral series `y ↦ ∑_{n ≥ 1} y ^ n / (n · n!)` is continuous on `ℝ`. -/
theorem continuous_tsum_pow_div_mul_factorial :
    Continuous fun y : ℝ ↦ ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) :=
  continuous_iff_continuousAt.mpr fun y ↦ (hasDerivAt_tsum_pow_div_mul_factorial y).continuousAt

/-- The removable-singularity extension of `(exp t - 1) / t` at `t = 0` is continuous on `ℝ`. -/
private theorem continuous_exp_sub_one_div_ext :
    Continuous fun t : ℝ ↦ if t = 0 then (1 : ℝ) else (Real.exp t - 1) / t := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : t = 0
  · subst ht
    rw [ContinuousAt]
    simp only [↓reduceIte]
    have hd : HasDerivAt Real.exp 1 0 := by simpa using Real.hasDerivAt_exp 0
    have hlim : Tendsto (fun u : ℝ ↦ (Real.exp u - 1) / u) (𝓝[≠] 0) (𝓝 1) := by
      simpa [hasDerivAt_iff_tendsto_slope_zero, smul_eq_mul, div_eq_inv_mul] using hd
    rw [Metric.tendsto_nhds] at hlim ⊢
    intro ε hε
    filter_upwards [eventually_nhdsWithin_iff.mp (hlim ε hε)] with u hu
    by_cases hu0 : u = 0
    · simp [hu0, hε]
    · simpa [hu0] using hu hu0
  · have hev : (fun u : ℝ ↦ if u = 0 then (1 : ℝ) else (Real.exp u - 1) / u) =ᶠ[𝓝 t]
        fun u : ℝ ↦ (Real.exp u - 1) / u := by
      filter_upwards [eventually_ne_nhds ht] with u hu
      simp [hu]
    exact ((Real.continuous_exp.sub continuous_const).continuousAt.div
      continuousAt_id ht).congr hev.symm

/-- The integrand `(exp t - 1) / t` is interval integrable on every interval. -/
theorem intervalIntegrable_exp_sub_one_div (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ ↦ (Real.exp t - 1) / t) volume a b := by
  refine (continuous_exp_sub_one_div_ext.intervalIntegrable a b).congr_ae ?_
  have hne : ∀ᵐ t ∂volume, t ≠ (0 : ℝ) := by rw [ae_iff]; simp
  filter_upwards [ae_restrict_of_ae hne] with t ht
  simp [ht]

/-- The integrand `(1 - exp (-t)) / t` is interval integrable on every interval. -/
theorem intervalIntegrable_one_sub_exp_neg_div (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ ↦ (1 - Real.exp (-t)) / t) volume a b := by
  have hcont : Continuous fun t : ℝ ↦ if t = 0 then (1 : ℝ) else (1 - Real.exp (-t)) / t := by
    refine (continuous_exp_sub_one_div_ext.comp continuous_neg).congr fun t ↦ ?_
    by_cases ht : t = 0
    · simp [ht]
    · simp [ht, neg_ne_zero.mpr ht]; ring
  refine (hcont.intervalIntegrable a b).congr_ae ?_
  have hne : ∀ᵐ t ∂volume, t ≠ (0 : ℝ) := by rw [ae_iff]; simp
  filter_upwards [ae_restrict_of_ae hne] with t ht
  simp [ht]

/-- The integral representation `∫₀^y (e^t - 1) / t dt = ∑_{n ≥ 1} y ^ n / (n · n!)`, valid for
every real `y`. -/
theorem integral_exp_sub_one_div_eq_tsum (y : ℝ) :
    (∫ t in (0 : ℝ)..y, (Real.exp t - 1) / t) =
      ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := y)
    (fun t _ ↦ hasDerivAt_tsum_pow_div_mul_factorial t)
    (continuous_exp_sub_one_div_ext.intervalIntegrable 0 y)
  have hzero : (∑' n : ℕ, (0 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) = 0 := by
    simp [zero_pow (Nat.succ_ne_zero _)]
  rw [hzero, sub_zero] at hFTC
  rw [← hFTC]
  refine intervalIntegral.integral_congr_ae ?_
  have hne : ∀ᵐ t ∂volume, t ≠ (0 : ℝ) := by rw [ae_iff]; simp
  filter_upwards [hne] with t ht _
  simp [ht]

/-- Integral representation of `principalLogIntegral` in terms of `∫₀^(log x) (e^t - 1) / t dt`. -/
theorem principalLogIntegral_eq_add_integral (x : ℝ) :
    principalLogIntegral x =
      Real.eulerMascheroniConstant + Real.log (Real.log x) +
        ∫ t in (0 : ℝ)..Real.log x, (Real.exp t - 1) / t := by
  rw [principalLogIntegral_def, integral_exp_sub_one_div_eq_tsum]

/-! ### Derivative and regularity -/

/-- The unoffset logarithmic integral has derivative `(log x)⁻¹` on `(0, 1) ∪ (1, ∞)`. -/
theorem hasDerivAt_principalLogIntegral {x : ℝ} (hx0 : 0 < x) (hx1 : x ≠ 1) :
    HasDerivAt principalLogIntegral (Real.log x)⁻¹ x := by
  have hlog_ne : Real.log x ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hx0 hx1
  have h1 : HasDerivAt (fun t : ℝ ↦ Real.log (Real.log t)) ((Real.log x)⁻¹ * x⁻¹) x :=
    (Real.hasDerivAt_log hlog_ne).comp x (Real.hasDerivAt_log hx0.ne')
  have h2 : HasDerivAt
      (fun t : ℝ ↦ ∑' n : ℕ, Real.log t ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)))
      (((Real.exp (Real.log x) - 1) / Real.log x) * x⁻¹) x := by
    have hc := (hasDerivAt_tsum_pow_div_mul_factorial (Real.log x)).comp x
      (Real.hasDerivAt_log hx0.ne')
    simp only [hlog_ne, ↓reduceIte] at hc
    exact hc
  have h3 := (h1.const_add Real.eulerMascheroniConstant).add h2
  refine h3.congr_deriv ?_
  rw [Real.exp_log hx0]
  field_simp [hlog_ne, hx0.ne']
  ring

/-- The unoffset logarithmic integral is differentiable on `(0, 1) ∪ (1, ∞)`. -/
theorem differentiableOn_principalLogIntegral :
    DifferentiableOn ℝ principalLogIntegral (Ioi 0 \ {1}) :=
  fun _ hx ↦ (hasDerivAt_principalLogIntegral hx.1 hx.2).differentiableAt.differentiableWithinAt

/-- The unoffset logarithmic integral is continuous on `(0, 1) ∪ (1, ∞)`. -/
theorem continuousOn_principalLogIntegral :
    ContinuousOn principalLogIntegral (Ioi 0 \ {1}) :=
  differentiableOn_principalLogIntegral.continuousOn

/-! ### Behaviour at `0⁺` and Euler–Mascheroni integral identity -/

/-- `t ↦ exp (-t) / t` is integrable on `(a, ∞)` for every `a > 0`. -/
theorem integrableOn_exp_neg_div_Ioi {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-t) / t) (Ioi a) := by
  have hexp : IntegrableOn (fun t : ℝ ↦ a⁻¹ * Real.exp ((-1 : ℝ) * t)) (Ioi a) :=
    (integrableOn_exp_mul_Ioi (by norm_num) a).const_mul a⁻¹
  have hmeas : AEStronglyMeasurable (fun t : ℝ ↦ Real.exp (-t) / t) (volume.restrict (Ioi a)) :=
    ((Real.continuous_exp.comp continuous_neg).measurable.div measurable_id).aestronglyMeasurable
  refine hexp.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ha.trans ht
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.exp_pos _), abs_of_pos ht0,
    neg_one_mul, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ ha ht.le) (Real.exp_pos _).le

/-- Integrability of `t ↦ exp (-t) * log t` on `(0, ∞)`. -/
theorem integrableOn_exp_neg_mul_log :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-t) * Real.log t) (Ioi 0) := by
  have h01 : IntegrableOn (fun t : ℝ ↦ Real.exp (-t) * Real.log t) (Ioo 0 1) := by
    have hlog : IntegrableOn Real.log (Ioo 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
        intervalIntegral.intervalIntegrable_log'
    refine hlog.norm.mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
    exact mul_le_of_le_one_left (abs_nonneg _) (Real.exp_le_one_iff.mpr (by linarith [ht.1]))
  have h1inf : IntegrableOn (fun t : ℝ ↦ Real.exp (-t) * Real.log t) (Ici 1) := by
    have hexp : IntegrableOn (fun t : ℝ ↦ 2 * Real.exp (-(1 / 2) * t)) (Ici 1) :=
      ((integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
        (integrableOn_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) 1)).const_mul 2
    refine hexp.mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have ht1 : 1 ≤ t := ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (Real.log_nonneg ht1)]
    have hlt : Real.log t ≤ t := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have ht_exp : t ≤ 2 * Real.exp ((1 / 2) * t) := by
      linarith [Real.add_one_le_exp ((1 / 2) * t)]
    calc Real.exp (-t) * Real.log t ≤ Real.exp (-t) * (2 * Real.exp ((1 / 2) * t)) :=
          mul_le_mul_of_nonneg_left (hlt.trans ht_exp) (Real.exp_pos _).le
      _ = 2 * Real.exp (-(1 / 2) * t) := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2; ring
  rw [← Ioo_union_Ici_eq_Ioi zero_lt_one]
  exact h01.union h1inf

/-- `(exp (c * ε) - 1) * log ε → 0` as `ε → 0⁺`. -/
private theorem tendsto_exp_mul_sub_one_mul_log_nhdsGT_zero (c : ℝ) :
    Tendsto (fun ε : ℝ ↦ (Real.exp (c * ε) - 1) * Real.log ε) (𝓝[>] 0) (𝓝 0) := by
  have hd : HasDerivAt (fun u : ℝ ↦ Real.exp (c * u)) c 0 :=
    ((Real.hasDerivAt_exp (c * 0)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_mul c)).congr_deriv
      (by simp)
  have h1 : Tendsto (fun ε : ℝ ↦ (Real.exp (c * ε) - 1) / ε) (𝓝[>] 0) (𝓝 c) := by
    have h := (hasDerivAt_iff_tendsto_slope_zero.mp hd).mono_left
      (nhdsWithin_mono (0 : ℝ) (s := Ioi 0) fun _ h ↦ ne_of_gt h)
    simpa [smul_eq_mul, div_eq_inv_mul] using h
  have h2 : Tendsto (fun ε : ℝ ↦ ε * Real.log ε) (𝓝[>] 0) (𝓝 0) := by
    simpa [Real.rpow_one, mul_comm] using tendsto_log_mul_rpow_nhdsGT_zero one_pos
  have hmul := h1.mul h2
  rw [mul_zero] at hmul
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  field_simp [ne_of_gt hε]

/-- `exp (-z) * log z → 0` as `z → +∞`. -/
private theorem tendsto_exp_neg_mul_log_atTop :
    Tendsto (fun z : ℝ ↦ Real.exp (-z) * Real.log z) atTop (𝓝 0) := by
  have h1 : Tendsto (fun z : ℝ ↦ Real.exp (-z) * z) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).congr fun z ↦ by rw [pow_one, mul_comm]
  refine squeeze_zero' ?_ ?_ h1
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
    exact mul_nonneg (Real.exp_pos _).le (Real.log_nonneg hz)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
    exact mul_le_mul_of_nonneg_left
      ((Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)) (Real.exp_pos _).le

/-- Integrability of `t ↦ c * exp (c * t) * log t` on `[0, w]` for `w > 0`. -/
private theorem integrableOn_mul_exp_mul_log_uIcc (c : ℝ) {w : ℝ} (hw : 0 < w) :
    IntegrableOn (fun t : ℝ ↦ c * Real.exp (c * t) * Real.log t) (uIcc 0 w) := by
  rw [uIcc_of_le hw.le, integrableOn_Icc_iff_integrableOn_Ioc]
  have hlog : IntegrableOn Real.log (Ioc 0 w) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hw.le).mp
      intervalIntegral.intervalIntegrable_log'
  refine (hlog.norm.const_mul (|c| * max 1 (Real.exp (c * w)))).mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)) (abs_nonneg _)
  rcases le_or_gt c 0 with hc | hc
  · exact (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hc ht.1.le)).trans
      (le_max_left _ _)
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hc.le)).trans (le_max_right _ _)

/-- Integrability of `(e^{c t} - 1) / t` on `[0, w]` for `w > 0`. -/
private theorem integrableOn_exp_mul_sub_one_div_uIcc (c : ℝ) {w : ℝ} (hw : 0 < w) :
    IntegrableOn (fun t : ℝ ↦ (Real.exp (c * t) - 1) / t) (uIcc 0 w) := by
  rw [uIcc_of_le hw.le, integrableOn_Icc_iff_integrableOn_Ioc]
  have hcont : Continuous fun t : ℝ ↦
      if t = 0 then c else (Real.exp (c * t) - 1) / t := by
    have hc0 : Continuous fun t : ℝ ↦
        c * (if c * t = 0 then (1 : ℝ) else (Real.exp (c * t) - 1) / (c * t)) :=
      continuous_const.mul (continuous_exp_sub_one_div_ext.comp
        (continuous_const.mul continuous_id))
    refine hc0.congr fun t ↦ ?_
    by_cases hc : c = 0
    · simp [hc]
    · by_cases ht : t = 0
      · simp [ht]
      · simp [ht, mul_ne_zero hc ht]; field_simp [hc, ht]
  refine ((intervalIntegrable_iff_integrableOn_Ioc_of_le hw.le).mp
    (hcont.intervalIntegrable 0 w)).congr_fun ?_ measurableSet_Ioc
  intro t ht; simp [ht.1.ne']

/-- Integration by parts on `(0, w]` connecting `(e^{c t} - 1) / t` and `c e^{c t} log t`. -/
private theorem integral_exp_mul_sub_one_div_add (c : ℝ) {w : ℝ} (hw : 0 < w) :
    (∫ t in (0 : ℝ)..w, (Real.exp (c * t) - 1) / t) +
        (∫ t in (0 : ℝ)..w, c * Real.exp (c * t) * Real.log t) =
      (Real.exp (c * w) - 1) * Real.log w := by
  have hint_log := integrableOn_mul_exp_mul_log_uIcc c hw
  have hint_g := integrableOn_exp_mul_sub_one_div_uIcc c hw
  have hε_eq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ t in ε..w, (Real.exp (c * t) - 1) / t) + (∫ t in ε..w, c * Real.exp (c * t) * Real.log t) =
        (Real.exp (c * w) - 1) * Real.log w - (Real.exp (c * ε) - 1) * Real.log ε := by
    filter_upwards [Ioo_mem_nhdsGT hw] with ε hε
    have hd : ∀ t ∈ uIcc ε w, HasDerivAt (fun u : ℝ ↦ (Real.exp (c * u) - 1) * Real.log u)
        ((Real.exp (c * t) - 1) / t + c * Real.exp (c * t) * Real.log t) t := by
      intro t ht
      rw [uIcc_of_le hε.2.le] at ht
      have h1 : HasDerivAt (fun u : ℝ ↦ Real.exp (c * u) - 1) (c * Real.exp (c * t)) t :=
        (((Real.hasDerivAt_exp (c * t)).comp t ((hasDerivAt_id t).const_mul c)).sub_const
          1).congr_deriv (by ring)
      exact (h1.mul (Real.hasDerivAt_log (hε.1.trans_le ht.1).ne')).congr_deriv (by ring)
    have hsub : uIcc ε w ⊆ uIcc 0 w :=
      uIcc_subset_uIcc (by rw [uIcc_of_le hw.le]; exact ⟨hε.1.le, hε.2.le⟩) right_mem_uIcc
    have hg' := hint_g.intervalIntegrable.mono_set hsub
    have hl' := hint_log.intervalIntegrable.mono_set hsub
    rw [← intervalIntegral.integral_add hg' hl',
      intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hg'.add hl')]
  have hmem : uIcc (0 : ℝ) w ∈ 𝓝[>] (0 : ℝ) := by
    rw [uIcc_of_le hw.le]
    exact mem_nhdsWithin.mpr ⟨Iio w, isOpen_Iio, hw, fun t ht ↦ ⟨ht.2.le, ht.1.le⟩⟩
  have hlim_g := ((intervalIntegral.continuousOn_primitive_interval_left hint_g) 0
    left_mem_uIcc).tendsto.mono_left (nhdsWithin_le_iff.mpr hmem)
  have hlim_log := ((intervalIntegral.continuousOn_primitive_interval_left hint_log) 0
    left_mem_uIcc).tendsto.mono_left (nhdsWithin_le_iff.mpr hmem)
  have hlim_rhs : Tendsto
      (fun ε : ℝ ↦ (Real.exp (c * w) - 1) * Real.log w - (Real.exp (c * ε) - 1) * Real.log ε)
      (𝓝[>] 0) (𝓝 ((Real.exp (c * w) - 1) * Real.log w)) := by
    simpa using tendsto_const_nhds.sub (tendsto_exp_mul_sub_one_mul_log_nhdsGT_zero c)
  exact tendsto_nhds_unique ((hlim_g.add hlim_log).congr' hε_eq) hlim_rhs

/-- Representation of `li (e^{-z})` for every real `z` via `∫₀^z e^{-t} log t dt`, obtained by
integrating the exponential-integral series by parts. -/
theorem principalLogIntegral_exp_neg (z : ℝ) :
    principalLogIntegral (Real.exp (-z)) =
      Real.eulerMascheroniConstant + Real.exp (-z) * Real.log z +
        ∫ t in (0 : ℝ)..z, Real.exp (-t) * Real.log t := by
  rw [principalLogIntegral_eq_add_integral, Real.log_exp, Real.log_neg_eq_log]
  rcases lt_trichotomy z 0 with hz | rfl | hz
  · have hw : 0 < -z := neg_pos.mpr hz
    have hneg : (∫ t in (0 : ℝ)..z, Real.exp (-t) * Real.log t) =
        -(∫ u in (0 : ℝ)..(-z), Real.exp u * Real.log u) := by
      have hcomp := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := -z)
        (f := fun t : ℝ ↦ Real.exp (-t) * Real.log t)
      simp only [neg_zero, neg_neg] at hcomp
      rw [intervalIntegral.integral_symm 0 z] at hcomp
      have heq : (∫ u in (0 : ℝ)..(-z), Real.exp u * Real.log (-u)) =
          ∫ u in (0 : ℝ)..(-z), Real.exp u * Real.log u :=
        intervalIntegral.integral_congr fun u _ ↦ by rw [Real.log_neg_eq_log]
      linarith
    have hibp := integral_exp_mul_sub_one_div_add 1 hw
    simp only [one_mul, Real.log_neg_eq_log] at hibp
    linarith
  · simp
  · have hneg : (∫ t in (0 : ℝ)..(-z), (Real.exp t - 1) / t) =
        ∫ t in (0 : ℝ)..z, (Real.exp (-t) - 1) / t := by
      have hcomp := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := z)
        (f := fun t : ℝ ↦ (Real.exp t - 1) / t)
      simp only [neg_zero] at hcomp
      rw [intervalIntegral.integral_symm 0 (-z)] at hcomp
      have heq : (∫ t in (0 : ℝ)..z, (Real.exp (-t) - 1) / -t) =
          -(∫ t in (0 : ℝ)..z, (Real.exp (-t) - 1) / t) := by
        rw [← intervalIntegral.integral_neg]
        exact intervalIntegral.integral_congr fun t _ ↦ by ring
      linarith
    have hibp := integral_exp_mul_sub_one_div_add (-1) hz
    simp only [neg_mul, one_mul, intervalIntegral.integral_neg] at hibp
    linarith

/-- Integration by parts on `[1, ∞)`: `∫₁^∞ e^{-t} log t dt = ∫₁^∞ e^{-t} / t dt`. -/
private theorem integral_exp_neg_mul_log_Ioi_one :
    (∫ t in Ioi (1 : ℝ), Real.exp (-t) * Real.log t) =
      ∫ t in Ioi (1 : ℝ), Real.exp (-t) / t := by
  have hint_exp_div : IntegrableOn (fun t : ℝ ↦ Real.exp (-t) / t) (Ioi 1) :=
    integrableOn_exp_neg_div_Ioi one_pos
  have hint_log1 : IntegrableOn (fun t : ℝ ↦ Real.exp (-t) * Real.log t) (Ioi 1) :=
    integrableOn_exp_neg_mul_log.mono_set (Ioi_subset_Ioi zero_le_one)
  have hR : ∀ᶠ R in atTop,
      (∫ t in (1 : ℝ)..R, Real.exp (-t) * Real.log t) - (∫ t in (1 : ℝ)..R, Real.exp (-t) / t) =
        -(Real.exp (-R) * Real.log R) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    have hd : ∀ t ∈ uIcc (1 : ℝ) R, HasDerivAt (fun u : ℝ ↦ -(Real.exp (-u) * Real.log u))
        (Real.exp (-t) * Real.log t - Real.exp (-t) / t) t := by
      intro t ht
      rw [uIcc_of_le hR] at ht
      have h1 : HasDerivAt (fun u : ℝ ↦ Real.exp (-u)) (-Real.exp (-t)) t :=
        ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).congr_deriv (by ring)
      exact (h1.mul (Real.hasDerivAt_log (zero_lt_one.trans_le ht.1).ne')).neg.congr_deriv (by ring)
    have h1 : IntervalIntegrable (fun t : ℝ ↦ Real.exp (-t) * Real.log t) volume 1 R :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr
        (hint_log1.mono_set Ioc_subset_Ioi_self)
    have h2 : IntervalIntegrable (fun t : ℝ ↦ Real.exp (-t) / t) volume 1 R :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr
        (hint_exp_div.mono_set Ioc_subset_Ioi_self)
    rw [← intervalIntegral.integral_sub h1 h2,
      intervalIntegral.integral_eq_sub_of_hasDerivAt hd (h1.sub h2)]
    simp
  have hlim1 := intervalIntegral_tendsto_integral_Ioi 1 hint_log1 tendsto_id
  have hlim2 := intervalIntegral_tendsto_integral_Ioi 1 hint_exp_div tendsto_id
  have hlim0 : Tendsto (fun R : ℝ ↦ -(Real.exp (-R) * Real.log R)) atTop (𝓝 0) := by
    simpa using tendsto_exp_neg_mul_log_atTop.neg
  linarith [tendsto_nhds_unique ((hlim1.sub hlim2).congr' hR) hlim0]

/-- **Integral representation of the Euler–Mascheroni constant**:
`γ = ∫₀¹ (1 - e^{-t}) / t dt - ∫₁^∞ e^{-t} / t dt`. -/
theorem eulerMascheroniConstant_eq_integral_sub_integral :
    Real.eulerMascheroniConstant =
      (∫ t in (0 : ℝ)..1, (1 - Real.exp (-t)) / t) -
        ∫ t in Ioi (1 : ℝ), Real.exp (-t) / t := by
  have hint_log1 : IntegrableOn (fun t : ℝ ↦ Real.exp (-t) * Real.log t) (Ioi 1) :=
    integrableOn_exp_neg_mul_log.mono_set (Ioi_subset_Ioi zero_le_one)
  have h01 : (∫ t in (0 : ℝ)..1, (1 - Real.exp (-t)) / t) =
      -(∫ t in Ioc (0 : ℝ) 1, Real.exp (-t) * Real.log t) := by
    have h := integral_exp_mul_sub_one_div_add (-1) one_pos
    simp only [neg_mul, one_mul, Real.log_one, mul_zero, intervalIntegral.integral_neg] at h
    have hi : (∫ t in (0 : ℝ)..1, Real.exp (-t) * Real.log t) =
        ∫ t in Ioc (0 : ℝ) 1, Real.exp (-t) * Real.log t :=
      intervalIntegral.integral_of_le zero_le_one
    have h1 : (∫ t in (0 : ℝ)..1, (Real.exp (-t) - 1) / t) =
        -(∫ t in (0 : ℝ)..1, (1 - Real.exp (-t)) / t) := by
      rw [← intervalIntegral.integral_neg]
      exact intervalIntegral.integral_congr fun t _ ↦ by ring
    linarith
  have hsplit : (∫ t in Ioi (0 : ℝ), Real.exp (-t) * Real.log t) =
      (∫ t in Ioc (0 : ℝ) 1, Real.exp (-t) * Real.log t) +
        ∫ t in Ioi (1 : ℝ), Real.exp (-t) * Real.log t := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (integrableOn_exp_neg_mul_log.mono_set Ioc_subset_Ioi_self) hint_log1,
      Ioc_union_Ioi_eq_Ioi zero_le_one]
  have hγ : Real.eulerMascheroniConstant = -(∫ t in Ioi (0 : ℝ), Real.exp (-t) * Real.log t) := by
    rw [Real.eulerMascheroniConstant_eq_neg_integral_log]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ mul_comm _ _
  linarith [integral_exp_neg_mul_log_Ioi_one]

/-- `li x → 0` as `x → 0⁺`. -/
theorem tendsto_principalLogIntegral_nhdsGT_zero :
    Tendsto principalLogIntegral (𝓝[>] 0) (𝓝 0) := by
  have hneglog : Tendsto (fun x : ℝ ↦ -Real.log x) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hint : Tendsto (fun z : ℝ ↦ ∫ t in (0 : ℝ)..z, Real.exp (-t) * Real.log t)
      atTop (𝓝 (-Real.eulerMascheroniConstant)) := by
    have h := intervalIntegral_tendsto_integral_Ioi 0 integrableOn_exp_neg_mul_log tendsto_id
    have hγ : (∫ t in Ioi (0 : ℝ), Real.exp (-t) * Real.log t) = -Real.eulerMascheroniConstant := by
      rw [Real.eulerMascheroniConstant_eq_neg_integral_log, neg_neg]
      exact setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ mul_comm _ _
    rwa [hγ] at h
  have hlim_z : Tendsto (fun z : ℝ ↦ Real.eulerMascheroniConstant + Real.exp (-z) * Real.log z +
      ∫ t in (0 : ℝ)..z, Real.exp (-t) * Real.log t) atTop (𝓝 0) := by
    have hsum := (tendsto_const_nhds (x := Real.eulerMascheroniConstant).add
      tendsto_exp_neg_mul_log_atTop).add hint
    rwa [add_zero, add_neg_cancel] at hsum
  refine (hlim_z.comp hneglog).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
  simp only [Function.comp_apply]
  rw [← principalLogIntegral_exp_neg (-Real.log x), neg_neg, Real.exp_log hx.1]

/-! ### Principal-value integral and offset relation with `Li` -/

/-- `(log t)⁻¹` is interval integrable on any interval inside `(-1, 1)`. -/
theorem intervalIntegrable_inv_log_of_mem_Ioo {a b : ℝ} (ha : a ∈ Ioo (-1 : ℝ) 1)
    (hb : b ∈ Ioo (-1 : ℝ) 1) :
    IntervalIntegrable (fun t : ℝ ↦ (Real.log t)⁻¹) volume a b := by
  set M : ℝ := max |a| |b|
  have hM1 : M < 1 := max_lt (abs_lt.mpr ha) (abs_lt.mpr hb)
  rcases (le_max_of_le_left (abs_nonneg a) : 0 ≤ M).eq_or_lt with hM0 | hMpos
  · have ha0 : a = 0 := abs_eq_zero.mp (le_antisymm ((le_max_left _ _).trans hM0.symm.le)
      (abs_nonneg a))
    have hb0 : b = 0 := abs_eq_zero.mp (le_antisymm ((le_max_right _ _).trans hM0.symm.le)
      (abs_nonneg b))
    rw [ha0, hb0]
  · have hlogM : Real.log M < 0 := Real.log_neg hMpos hM1
    refine IntervalIntegrable.mono_fun'
      (g := fun _ : ℝ ↦ (-Real.log M)⁻¹) intervalIntegrable_const (by fun_prop) ?_
    have hne : ∀ᵐ t ∂volume, t ≠ (0 : ℝ) := by rw [ae_iff]; simp
    filter_upwards [ae_restrict_of_ae hne, ae_restrict_mem measurableSet_uIoc] with t ht0 ht
    have htM : |t| ≤ M := by
      have hmem : t ∈ uIcc a b := Ioc_subset_Icc_self ht
      rw [abs_le]
      rcases mem_uIcc.mp hmem with h | h
      · exact ⟨by linarith [neg_abs_le a, le_max_left |a| |b|],
          h.2.trans ((le_abs_self b).trans (le_max_right _ _))⟩
      · exact ⟨by linarith [neg_abs_le b, le_max_right |a| |b|],
          h.2.trans ((le_abs_self a).trans (le_max_left _ _))⟩
    have hlt : Real.log t ≤ Real.log M := by
      rw [← Real.log_abs]
      exact Real.log_le_log (abs_pos.mpr ht0) htM
    rw [Real.norm_eq_abs, abs_inv, abs_of_neg (hlt.trans_lt hlogM)]
    exact inv_anti₀ (neg_pos.mpr hlogM) (neg_le_neg hlt)

/-- On `(0, 1)`, the unoffset logarithmic integral is the ordinary integral `∫₀ˣ dt / log t`. -/
theorem principalLogIntegral_eq_integral {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    principalLogIntegral x = ∫ t in (0 : ℝ)..x, (Real.log t)⁻¹ := by
  have h0mem : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, zero_lt_one⟩
  have hint : IntegrableOn (fun t : ℝ ↦ (Real.log t)⁻¹) (uIcc 0 x) := by
    rw [uIcc_of_le hx0.le, integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hx0.le).mp
      (intervalIntegrable_inv_log_of_mem_Ioo h0mem ⟨by linarith, hx1⟩)
  have hmem : uIcc (0 : ℝ) x ∈ 𝓝[>] (0 : ℝ) := by
    rw [uIcc_of_le hx0.le]
    exact mem_nhdsWithin.mpr ⟨Iio x, isOpen_Iio, hx0, fun t ht ↦ ⟨ht.2.le, ht.1.le⟩⟩
  have hlim_int : Tendsto (fun δ : ℝ ↦ ∫ t in δ..x, (Real.log t)⁻¹) (𝓝[>] 0)
      (𝓝 (∫ t in (0 : ℝ)..x, (Real.log t)⁻¹)) :=
    ((intervalIntegral.continuousOn_primitive_interval_left hint) 0
      left_mem_uIcc).tendsto.mono_left (nhdsWithin_le_iff.mpr hmem)
  have hlim_rhs : Tendsto (fun δ : ℝ ↦ principalLogIntegral x - principalLogIntegral δ)
      (𝓝[>] 0) (𝓝 (principalLogIntegral x)) := by
    simpa using tendsto_const_nhds.sub tendsto_principalLogIntegral_nhdsGT_zero
  have hδ : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∫ t in δ..x, (Real.log t)⁻¹) = principalLogIntegral x - principalLogIntegral δ := by
    filter_upwards [Ioo_mem_nhdsGT hx0] with δ hδ
    have hd : ∀ t ∈ uIcc δ x, HasDerivAt principalLogIntegral (Real.log t)⁻¹ t := by
      intro t ht
      rw [uIcc_of_le hδ.2.le] at ht
      exact hasDerivAt_principalLogIntegral (hδ.1.trans_le ht.1) (ht.2.trans_lt hx1).ne
    have hsub : IntervalIntegrable (fun t : ℝ ↦ (Real.log t)⁻¹) volume δ x :=
      intervalIntegrable_inv_log_of_mem_Ioo ⟨by linarith [hδ.1], hδ.2.trans hx1⟩ ⟨by linarith, hx1⟩
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd hsub
  exact tendsto_nhds_unique (hlim_rhs.congr' (hδ.mono fun _ h ↦ h.symm)) hlim_int

/-- Symmetric cancellation of the double-logarithm singularity:
`log |log (1 - ε)| - log |log (1 + ε)| → 0` as `ε → 0⁺`. -/
private theorem tendsto_log_log_one_sub_sub_log_log_one_add :
    Tendsto (fun ε : ℝ ↦ Real.log (Real.log (1 - ε)) - Real.log (Real.log (1 + ε)))
      (𝓝[>] 0) (𝓝 0) := by
  have hlog_add : Tendsto (fun ε : ℝ ↦ Real.log (1 + ε) / ε) (𝓝[>] 0) (𝓝 1) := by
    have hd : HasDerivAt Real.log 1 1 := by simpa using Real.hasDerivAt_log one_ne_zero
    have h := (hasDerivAt_iff_tendsto_slope_zero.mp hd).mono_left
      (nhdsWithin_mono (0 : ℝ) (s := Ioi 0) fun _ h ↦ ne_of_gt h)
    simpa [smul_eq_mul, div_eq_inv_mul] using h
  have hlog_sub : Tendsto (fun ε : ℝ ↦ -(Real.log (1 - ε) / ε)) (𝓝[>] 0) (𝓝 1) := by
    have h1 : HasDerivAt (fun u : ℝ ↦ 1 - u) (-1) 0 :=
      ((hasDerivAt_id (0 : ℝ)).const_sub 1).congr_deriv (by norm_num)
    have hd : HasDerivAt (fun u : ℝ ↦ -Real.log (1 - u)) 1 0 :=
      ((Real.hasDerivAt_log (by norm_num : (1 : ℝ) - 0 ≠ 0)).comp (0 : ℝ) h1).neg.congr_deriv
        (by norm_num)
    have h := (hasDerivAt_iff_tendsto_slope_zero.mp hd).mono_left
      (nhdsWithin_mono (0 : ℝ) (s := Ioi 0) fun _ h ↦ ne_of_gt h)
    simpa [smul_eq_mul, div_eq_inv_mul] using h
  have hdiv := hlog_sub.div hlog_add one_ne_zero
  rw [div_one] at hdiv
  have hcomp := (Real.continuousAt_log one_ne_zero).tendsto.comp hdiv
  rw [Real.log_one] at hcomp
  refine hcomp.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
  have h1 : Real.log (1 - ε) < 0 := Real.log_neg (by linarith [hε.2]) (by linarith [hε.1])
  have h2 : 0 < Real.log (1 + ε) := Real.log_pos (by linarith [hε.1])
  simp only [Function.comp_apply, Pi.div_apply]
  rw [← Real.log_neg_eq_log (Real.log (1 - ε)),
    ← Real.log_div (neg_ne_zero.mpr h1.ne) h2.ne']
  congr 1
  field_simp [hε.1.ne']

/-- The symmetric logarithmic cancellation `li (1 - ε) - li (1 + ε) → 0` as `ε → 0⁺`. -/
private theorem tendsto_principalLogIntegral_one_sub_sub_one_add :
    Tendsto (fun ε : ℝ ↦ principalLogIntegral (1 - ε) - principalLogIntegral (1 + ε))
      (𝓝[>] 0) (𝓝 0) := by
  have hser : Tendsto (fun ε : ℝ ↦
      (∑' n : ℕ, Real.log (1 - ε) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) -
        (∑' n : ℕ, Real.log (1 + ε) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))))
      (𝓝[>] 0) (𝓝 0) := by
    have hsub_c : ContinuousAt (fun ε : ℝ ↦ Real.log (1 - ε)) 0 :=
      (Real.continuousAt_log (by norm_num : (1 : ℝ) - 0 ≠ 0)).comp
        (f := fun ε : ℝ ↦ 1 - ε) (by fun_prop)
    have hadd_c : ContinuousAt (fun ε : ℝ ↦ Real.log (1 + ε)) 0 :=
      (Real.continuousAt_log (by norm_num : (1 : ℝ) + 0 ≠ 0)).comp
        (f := fun ε : ℝ ↦ 1 + ε) (by fun_prop)
    have hc1 := continuous_tsum_pow_div_mul_factorial.continuousAt.comp hsub_c
    have hc2 := continuous_tsum_pow_div_mul_factorial.continuousAt.comp hadd_c
    have hdiff := (hc1.sub hc2).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    have hval : (∑' n : ℕ, Real.log (1 - (0 : ℝ)) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) -
        (∑' n : ℕ, Real.log (1 + (0 : ℝ)) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) = 0 := by
      simp
    refine (hdiff.congr fun ε ↦ rfl).trans ?_
    simp only [Pi.sub_apply, Function.comp_apply, hval]
    exact le_rfl
  have hsum := tendsto_log_log_one_sub_sub_log_log_one_add.add hser
  rw [add_zero] at hsum
  refine hsum.congr fun ε ↦ ?_
  simp only [principalLogIntegral_def]
  ring

/-- **Cauchy principal value**: for `x > 1`, `li x` is the limit as `ε → 0⁺` of
`∫₀^(1 - ε) dt / log t + ∫_(1 + ε)^x dt / log t`. -/
theorem tendsto_principalLogIntegral_pv {x : ℝ} (hx : 1 < x) :
    Tendsto
      (fun ε : ℝ ↦
        (∫ t in (0 : ℝ)..(1 - ε), (Real.log t)⁻¹) + ∫ t in (1 + ε)..x, (Real.log t)⁻¹)
      (𝓝[>] 0) (𝓝 (principalLogIntegral x)) := by
  have hlim : Tendsto
      (fun ε : ℝ ↦ principalLogIntegral x +
        (principalLogIntegral (1 - ε) - principalLogIntegral (1 + ε)))
      (𝓝[>] 0) (𝓝 (principalLogIntegral x)) := by
    simpa using tendsto_const_nhds.add tendsto_principalLogIntegral_one_sub_sub_one_add
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min zero_lt_one (sub_pos.mpr hx))] with ε hε
  have hε1 : ε < 1 := hε.2.trans_le (min_le_left _ _)
  have hεx : 1 + ε < x := by linarith [hε.2.trans_le (min_le_right _ _)]
  have hleft : (∫ t in (0 : ℝ)..(1 - ε), (Real.log t)⁻¹) = principalLogIntegral (1 - ε) :=
    (principalLogIntegral_eq_integral (by linarith) (by linarith [hε.1])).symm
  have hright : (∫ t in (1 + ε)..x, (Real.log t)⁻¹) =
      principalLogIntegral x - principalLogIntegral (1 + ε) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht ↦ ?_) ?_
    · rw [uIcc_of_le hεx.le] at ht
      have ht1 : 1 < t := by linarith [hε.1, ht.1]
      exact hasDerivAt_principalLogIntegral (zero_lt_one.trans ht1) ht1.ne'
    · simpa only [pow_one] using intervalIntegrable_inv_log_pow 1 (by linarith [hε.1]) hx
  linarith

/-- **Offset relation**: for every `x > 1`, `Li x = li x - li 2`. -/
theorem logIntegral_eq_principalLogIntegral_sub {x : ℝ} (hx : 1 < x) :
    logIntegral x = principalLogIntegral x - principalLogIntegral 2 := by
  rw [logIntegral_def]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht ↦ ?_) ?_
  · have ht1 : 1 < t := by
      rcases mem_uIcc.mp ht with h | h
      · exact one_lt_two.trans_le h.1
      · exact hx.trans_le h.1
    exact hasDerivAt_principalLogIntegral (zero_lt_one.trans ht1) ht1.ne'
  · simpa only [pow_one] using intervalIntegrable_inv_log_pow 1 one_lt_two hx

/-- Equivalent form of the offset relation: `li x = Li x + li 2` for every `x > 1`. -/
theorem principalLogIntegral_eq_logIntegral_add {x : ℝ} (hx : 1 < x) :
    principalLogIntegral x = logIntegral x + principalLogIntegral 2 := by
  linarith [logIntegral_eq_principalLogIntegral_sub hx]

/-! ### Monotonicity, limits, sign, and Soldner's constant -/

/-- `li` is strictly decreasing on `(0, 1)`. -/
theorem strictAntiOn_principalLogIntegral :
    StrictAntiOn principalLogIntegral (Ioo 0 1) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioo 0 1)
    (continuousOn_principalLogIntegral.mono fun _ hx ↦ ⟨hx.1, hx.2.ne⟩) fun x hx ↦ ?_
  rw [interior_Ioo] at hx
  rw [(hasDerivAt_principalLogIntegral hx.1 hx.2.ne).deriv]
  exact inv_neg''.mpr (Real.log_neg hx.1 hx.2)

/-- `li` is strictly increasing on `(1, ∞)`. -/
theorem strictMonoOn_principalLogIntegral :
    StrictMonoOn principalLogIntegral (Ioi 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 1)
    (continuousOn_principalLogIntegral.mono fun _ hx ↦ ⟨zero_lt_one.trans hx, hx.ne'⟩)
    fun x hx ↦ ?_
  rw [interior_Ioi] at hx
  rw [(hasDerivAt_principalLogIntegral (zero_lt_one.trans hx) hx.ne').deriv]
  exact inv_pos.mpr (Real.log_pos hx)

/-- `li x < 0` for every `0 < x < 1`. -/
theorem principalLogIntegral_neg_of_lt_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    principalLogIntegral x < 0 := by
  have hhalf : principalLogIntegral x < principalLogIntegral (x / 2) :=
    strictAntiOn_principalLogIntegral ⟨half_pos hx0, by linarith⟩ ⟨hx0, hx1⟩ (half_lt_self hx0)
  have hle : principalLogIntegral (x / 2) ≤ 0 := by
    refine ge_of_tendsto tendsto_principalLogIntegral_nhdsGT_zero ?_
    filter_upwards [Ioo_mem_nhdsGT (half_pos hx0)] with t ht
    exact (strictAntiOn_principalLogIntegral ⟨ht.1, by linarith [ht.2]⟩
      ⟨half_pos hx0, by linarith⟩ ht.2).le
  exact hhalf.trans_le hle

/-- `li x → -∞` as `x → 1` along `𝓝[≠] 1`. -/
theorem tendsto_principalLogIntegral_nhdsNE_one :
    Tendsto principalLogIntegral (𝓝[≠] 1) atBot := by
  have hlog0 : Tendsto Real.log (𝓝[≠] 1) (𝓝 0) := by
    simpa only [Real.log_one] using
      (Real.continuousAt_log one_ne_zero).tendsto.mono_left (nhdsWithin_le_nhds (s := {1}ᶜ))
  have hlog : Tendsto Real.log (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hlog0 ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds zero_lt_one)] with x hx1 hx0
    exact Real.log_ne_zero_of_pos_of_ne_one hx0 hx1
  have h1 : Tendsto (fun x : ℝ ↦ Real.eulerMascheroniConstant + Real.log (Real.log x))
      (𝓝[≠] 1) atBot :=
    tendsto_atBot_add_const_left _ _ (Real.tendsto_log_nhdsNE_zero.comp hlog)
  have h2 : Tendsto (fun x : ℝ ↦
      ∑' n : ℕ, Real.log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)))
      (𝓝[≠] 1) (𝓝 0) := by
    have h0 : (∑' n : ℕ, (0 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) = 0 := by
      simp [zero_pow (Nat.succ_ne_zero _)]
    have hc := continuous_tsum_pow_div_mul_factorial.tendsto 0
    rw [h0] at hc
    exact hc.comp hlog0
  exact h1.atBot_add h2

/-- `li x → -∞` as `x → 1⁺`. -/
theorem tendsto_principalLogIntegral_nhdsGT_one :
    Tendsto principalLogIntegral (𝓝[>] 1) atBot :=
  tendsto_principalLogIntegral_nhdsNE_one.mono_left
    (nhdsWithin_mono 1 fun _ (hx : 1 < _) ↦ ne_of_gt hx)

/-- `li x → -∞` as `x → 1⁻`. -/
theorem tendsto_principalLogIntegral_nhdsLT_one :
    Tendsto principalLogIntegral (𝓝[<] 1) atBot :=
  tendsto_principalLogIntegral_nhdsNE_one.mono_left
    (nhdsWithin_mono 1 fun _ (hx : _ < 1) ↦ ne_of_lt hx)

/-- `li x → +∞` as `x → +∞`. -/
theorem tendsto_principalLogIntegral_atTop :
    Tendsto principalLogIntegral atTop atTop := by
  have hLi : Tendsto logIntegral atTop atTop := by
    have h : Tendsto (fun x : ℝ ↦ (x - 2) / Real.log x) atTop atTop := by
      have h1 : Tendsto (fun x : ℝ ↦ x / Real.log x + (-2 : ℝ) / Real.log x) atTop atTop :=
        tendsto_div_log_atTop.atTop_add
          (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop)
      exact h1.congr fun x ↦ by ring
    exact tendsto_atTop_mono' atTop
      (eventually_ge_atTop (2 : ℝ) |>.mono fun _ hx ↦ le_logIntegral hx) h
  refine (tendsto_atTop_add_const_right _ (principalLogIntegral 2) hLi).congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact (principalLogIntegral_eq_logIntegral_add hx).symm

/-- **Soldner's constant**: `li` has a unique zero in `(1, ∞)`. -/
theorem existsUnique_principalLogIntegral_eq_zero :
    ∃! μ ∈ Ioi (1 : ℝ), principalLogIntegral μ = 0 := by
  obtain ⟨a, ha1, ha0⟩ : ∃ a : ℝ, 1 < a ∧ principalLogIntegral a < 0 := by
    have h := (tendsto_principalLogIntegral_nhdsGT_one.eventually (eventually_lt_atBot 0)).and
      self_mem_nhdsWithin
    obtain ⟨a, ha0, ha1⟩ := h.exists
    exact ⟨a, ha1, ha0⟩
  obtain ⟨b, hba, hb0⟩ : ∃ b : ℝ, a < b ∧ 0 < principalLogIntegral b := by
    have h := (tendsto_principalLogIntegral_atTop.eventually (eventually_gt_atTop 0)).and
      (eventually_gt_atTop a)
    obtain ⟨b, hb0, hba⟩ := h.exists
    exact ⟨b, hba, hb0⟩
  have hcont : ContinuousOn principalLogIntegral (Icc a b) :=
    continuousOn_principalLogIntegral.mono fun t ht ↦
      ⟨zero_lt_one.trans (ha1.trans_le ht.1), (ha1.trans_le ht.1).ne'⟩
  obtain ⟨μ, hμab, hμ0⟩ := intermediate_value_Icc hba.le hcont ⟨ha0.le, hb0.le⟩
  refine ⟨μ, ⟨ha1.trans_le hμab.1, hμ0⟩, fun y ⟨hy1, hy0⟩ ↦ ?_⟩
  exact strictMonoOn_principalLogIntegral.injOn hy1 (ha1.trans_le hμab.1) (hy0.trans hμ0.symm)

end TauCeti.Real
