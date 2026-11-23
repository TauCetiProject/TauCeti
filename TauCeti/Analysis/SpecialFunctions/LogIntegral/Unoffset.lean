/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import TauCeti.Analysis.SpecialFunctions.LogIntegral.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import TauCeti.Analysis.SpecialFunctions.Exp.Limits
import TauCeti.Analysis.SpecialFunctions.Log.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Log.Bounds
import TauCeti.Analysis.SpecialFunctions.Log.InvLog

/-!
# The unoffset logarithmic integral

This file defines the unoffset logarithmic integral
`li x = γ + log |log x| + ∑' n, (log x) ^ (n + 1) / ((n + 1) * (n + 1)!)`,
which equals the exponential integral `Ei (log x)` for `x > 0`, `x ≠ 1` (at `x = 1`, where
`log x = 0`, the definition takes a junk value).

## Main declarations

* `TauCeti.Real.unoffsetLogIntegral`: the unoffset logarithmic integral `li`.
* `TauCeti.Real.hasDerivAt_unoffsetLogIntegral`: `li' x = (log x)⁻¹` for `x > 0`, `x ≠ 1`.
* `TauCeti.Real.tendsto_unoffsetLogIntegral_nhdsGT_zero`: `li x → 0` as `x → 0⁺`.
* `TauCeti.Real.unoffsetLogIntegral_eq_integral`: `li x = ∫ t in 0..x, (log t)⁻¹` for
  `0 < x < 1`.
* `TauCeti.Real.tendsto_principalValue_inv_log`: the Cauchy principal value
  `∫ t in 0..(1 - ε), (log t)⁻¹ + ∫ t in (1 + ε)..x, (log t)⁻¹ → li x` for `x > 1`.
* `TauCeti.Real.logIntegral_eq_unoffsetLogIntegral_sub`: `Li x = li x - li 2` for `x > 1`.
* `TauCeti.Real.strictAntiOn_unoffsetLogIntegral_Ioo`,
  `TauCeti.Real.strictMonoOn_unoffsetLogIntegral_Ioi`: `li` decreases on `(0, 1)` (where it is
  negative) and increases on `(1, ∞)` from `-∞` to `+∞`.
* `TauCeti.Real.existsUnique_unoffsetLogIntegral_eq_zero`: Soldner's constant, the unique zero
  of `li` on `(1, ∞)`.
* `TauCeti.Real.unoffsetLogIntegral_sub_sum_isBigO`,
  `TauCeti.Real.unoffsetLogIntegral_isEquivalent_div_log`: asymptotic expansion to arbitrary order
  and `li x ~ Li x ~ x / log x` as `x → ∞`.
-/

public section

namespace TauCeti.Real

open Asymptotics Filter MeasureTheory Set
open scoped Topology Nat

/-! ### The entire series `∑_{n ≥ 1} yⁿ / (n · n!)` -/

/-- The series `∑' n, y ^ (n + 1) / ((n + 1) * (n + 1)!)` is summable for every real `y`. -/
theorem summable_pow_div_mul_factorial (y : ℝ) :
    Summable fun n : ℕ ↦ y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ)) := by
  refine .of_norm_bounded ((Real.summable_pow_div_factorial |y|).mul_left |y|) fun n ↦ ?_
  have hpos : (0 : ℝ) < ((n : ℝ) + 1) * ((n + 1).factorial : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos, ← pow_abs]
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  calc |y| ^ (n + 1) / (((n : ℝ) + 1) * (((n : ℝ) + 1) * (n ! : ℝ)))
      ≤ |y| ^ (n + 1) / (1 * (1 * (n ! : ℝ))) := by
        gcongr <;> linarith
    _ = |y| * (|y| ^ n / (n ! : ℝ)) := by
        rw [pow_succ']
        ring

/-- The derivative of `z ↦ ∑' n, z ^ (n + 1) / ((n + 1) * (n + 1)!)` is `(e^y - 1) / y`
(with value `1` at `y = 0`). -/
theorem hasDerivAt_tsum_pow_div_mul_factorial (y : ℝ) :
    HasDerivAt
      (fun z : ℝ ↦ ∑' n : ℕ, z ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ)))
      (if y = 0 then 1 else (Real.exp y - 1) / y) y := by
  let R : ℝ := |y| + 1
  let g (n : ℕ) (z : ℝ) : ℝ := z ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ))
  let g' (n : ℕ) (z : ℝ) : ℝ := z ^ n / ((n + 1).factorial : ℝ)
  have hg : ∀ n : ℕ, ∀ z ∈ Metric.ball (0 : ℝ) R, HasDerivAt (g n) (g' n z) z := by
    intro n z _
    have hpow : HasDerivAt (fun w : ℝ ↦ w ^ (n + 1)) (((n + 1 : ℕ) : ℝ) * z ^ n) z :=
      hasDerivAt_pow (n + 1) z
    refine (hpow.div_const (((n : ℝ) + 1) * ((n + 1).factorial : ℝ))).congr_deriv ?_
    dsimp only [g']
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp [hn1]
  have hg' : ∀ n : ℕ, ∀ z ∈ Metric.ball (0 : ℝ) R, ‖g' n z‖ ≤ R ^ n / (n ! : ℝ) := by
    intro n z hz
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hz
    have hfac : (n ! : ℝ) ≤ ((n + 1).factorial : ℝ) :=
      Nat.cast_le.mpr (Nat.factorial_le (Nat.le_succ n))
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((n + 1).factorial : ℝ)),
      ← pow_abs]
    calc |z| ^ n / ((n + 1).factorial : ℝ)
        ≤ R ^ n / ((n + 1).factorial : ℝ) := by gcongr
      _ ≤ R ^ n / (n ! : ℝ) := by gcongr
  have hsum := hasDerivAt_tsum_of_isPreconnected (Real.summable_pow_div_factorial R)
    Metric.isOpen_ball (convex_ball (0 : ℝ) R).isPreconnected hg hg'
    (Metric.mem_ball_self (by positivity : 0 < R))
    (by simp [g]) (Metric.mem_ball.mpr (by rw [Real.dist_eq, sub_zero]; linarith))
  refine hsum.congr_deriv ?_
  by_cases hy : y = 0
  · subst hy
    simp only [↓reduceIte, g']
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      simp [zero_pow hn]
  · simp only [hy, ↓reduceIte, g']
    have hsumm : Summable fun n : ℕ ↦ y ^ n / ((n + 1).factorial : ℝ) := by
      refine .of_norm_bounded (Real.summable_pow_div_factorial |y|) fun n ↦ ?_
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((n + 1).factorial : ℝ)),
        ← pow_abs]
      gcongr
      exact Nat.le_succ n
    have hexp : ∑' n : ℕ, y ^ n / (n ! : ℝ) = Real.exp y := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    have hsplit := (Real.summable_pow_div_factorial y).tsum_eq_zero_add
    rw [hexp, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at hsplit
    have hmul : y * ∑' n : ℕ, y ^ n / ((n + 1).factorial : ℝ) = Real.exp y - 1 := by
      rw [← hsumm.tsum_mul_left]
      have hcongr : (fun n : ℕ ↦ y * (y ^ n / ((n + 1).factorial : ℝ))) =
          fun n : ℕ ↦ y ^ (n + 1) / ((n + 1).factorial : ℝ) := by
        ext n
        rw [pow_succ']
        ring
      rw [hcongr]
      linarith
    exact (eq_div_iff hy).mpr (by linarith)

/-- The filled-in quotient `(e^u - 1) / u` (with value `1` at `0`) is continuous on `ℝ`. -/
theorem continuous_exp_sub_one_div :
    Continuous fun u : ℝ ↦ if u = 0 then (1 : ℝ) else (Real.exp u - 1) / u := by
  rw [continuous_iff_continuousAt]
  intro u
  by_cases hu : u = 0
  · subst hu
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
    simp only [↓reduceIte]
    have hlim : Tendsto (fun t : ℝ ↦ (Real.exp t - 1) / t) (𝓝[≠] 0) (𝓝 1) := by
      simpa using Real.tendsto_exp_mul_sub_one_div 1
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := mem_compl_singleton_iff.mp ht
    simp [ht0]
  · have hcont : ContinuousAt (fun t : ℝ ↦ (Real.exp t - 1) / t) u := by
      fun_prop (disch := exact hu)
    refine hcont.congr ?_
    filter_upwards [eventually_ne_nhds hu] with t ht
    simp [ht]

/-- Integrating `(e^u - 1) / u` from `0` to `y` gives the entire series
`∑' n, y ^ (n + 1) / ((n + 1) * (n + 1)!)`. -/
theorem integral_exp_sub_one_div_eq_tsum (y : ℝ) :
    ∫ u in (0 : ℝ)..y, (Real.exp u - 1) / u =
      ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ)) := by
  let f : ℝ → ℝ := fun u ↦ if u = 0 then 1 else (Real.exp u - 1) / u
  have hcont : Continuous f := continuous_exp_sub_one_div
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ ↦ hasDerivAt_tsum_pow_div_mul_factorial u) (hcont.intervalIntegrable 0 y)
  have h0 : ∑' n : ℕ, (0 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ)) = 0 := by
    simp
  rw [h0, sub_zero] at hFTC
  rw [← hFTC]
  refine intervalIntegral.integral_congr_ae ?_
  have hne : ∀ᵐ u : ℝ ∂volume, u ≠ 0 := ae_iff.mpr (by simp)
  filter_upwards [hne] with u hu _
  simp [hu]

/-- Integrating `(1 - e^{-t}) / t` from `0` to `z` gives
`-∑' n, (-z) ^ (n + 1) / ((n + 1) * (n + 1)!)`. -/
theorem integral_one_sub_exp_neg_div_eq (z : ℝ) :
    ∫ t in (0 : ℝ)..z, (1 - Real.exp (-t)) / t =
      -∑' n : ℕ, (-z) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ)) := by
  have hcomp := intervalIntegral.integral_comp_neg
    (f := fun u : ℝ ↦ (Real.exp u - 1) / u) (a := (0 : ℝ)) (b := z)
  simp only [neg_zero] at hcomp
  have heq : (fun t : ℝ ↦ (Real.exp (-t) - 1) / (-t)) = fun t : ℝ ↦ (1 - Real.exp (-t)) / t := by
    ext t
    ring
  rw [heq, intervalIntegral.integral_symm 0 (-z)] at hcomp
  rw [hcomp, integral_exp_sub_one_div_eq_tsum (-z)]

/-! ### The unoffset logarithmic integral and its derivative -/

/-- The **unoffset logarithmic integral**
`li x = γ + log |log x| + ∑' n, (log x) ^ (n + 1) / ((n + 1) * (n + 1)!)`.

In Mathlib, `Real.log` satisfies `Real.log (-y) = Real.log y`, so `Real.log (Real.log x)` equals
`log |log x|` for every `x > 0` with `x ≠ 1`. At `x = 1`, where `log x = 0`, the definition takes
a junk value. For `0 < x < 1` it equals `∫ t in 0..x, (log t)⁻¹`, and for `x > 1` it is the
Cauchy principal value `lim_{ε → 0⁺} (∫ t in 0..(1 - ε), (log t)⁻¹ + ∫ t in (1 + ε)..x, (log t)⁻¹)`
and satisfies `Li x = li x - li 2`. -/
noncomputable def unoffsetLogIntegral (x : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (Real.log x) +
    ∑' n : ℕ, Real.log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ))

/-- Defining equation of `TauCeti.Real.unoffsetLogIntegral`. -/
theorem unoffsetLogIntegral_def (x : ℝ) :
    unoffsetLogIntegral x =
      Real.eulerMascheroniConstant + Real.log (Real.log x) +
        ∑' n : ℕ, Real.log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ)) :=
  (rfl)

/-- The unoffset logarithmic integral has derivative `(log x)⁻¹` for `x > 0`, `x ≠ 1`. -/
theorem hasDerivAt_unoffsetLogIntegral {x : ℝ} (hx₀ : 0 < x) (hx₁ : x ≠ 1) :
    HasDerivAt unoffsetLogIntegral (Real.log x)⁻¹ x := by
  have hlog_ne : Real.log x ≠ 0 := Real.log_ne_zero.mpr ⟨hx₀.ne', hx₁, by linarith⟩
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx₀.ne'
  have h1 : HasDerivAt (fun t : ℝ ↦ Real.eulerMascheroniConstant + Real.log (Real.log t))
      (x⁻¹ / Real.log x) x := by
    simpa [div_eq_mul_inv, mul_comm] using
      ((Real.hasDerivAt_log hlog_ne).comp x hlog).const_add Real.eulerMascheroniConstant
  have h2 := (hasDerivAt_tsum_pow_div_mul_factorial (Real.log x)).comp x hlog
  simp only [hlog_ne, ↓reduceIte, Real.exp_log hx₀] at h2
  refine (h1.add h2).congr_deriv ?_
  change x⁻¹ / Real.log x + (x - 1) / Real.log x * x⁻¹ = (Real.log x)⁻¹
  field_simp [hx₀.ne', hlog_ne]
  ring

/-- The unoffset logarithmic integral is differentiable on `(0, 1)`. -/
theorem differentiableOn_unoffsetLogIntegral_Ioo :
    DifferentiableOn ℝ unoffsetLogIntegral (Ioo 0 1) :=
  fun _ hx ↦ (hasDerivAt_unoffsetLogIntegral hx.1 hx.2.ne).differentiableAt.differentiableWithinAt

/-- The unoffset logarithmic integral is differentiable on `(1, ∞)`. -/
theorem differentiableOn_unoffsetLogIntegral_Ioi :
    DifferentiableOn ℝ unoffsetLogIntegral (Ioi 1) :=
  fun _ hx ↦
    (hasDerivAt_unoffsetLogIntegral (zero_lt_one.trans hx)
      hx.ne').differentiableAt.differentiableWithinAt

/-- The unoffset logarithmic integral is continuous on `(0, 1)`. -/
theorem continuousOn_unoffsetLogIntegral_Ioo : ContinuousOn unoffsetLogIntegral (Ioo 0 1) :=
  differentiableOn_unoffsetLogIntegral_Ioo.continuousOn

/-- The unoffset logarithmic integral is continuous on `(1, ∞)`. -/
theorem continuousOn_unoffsetLogIntegral_Ioi : ContinuousOn unoffsetLogIntegral (Ioi 1) :=
  differentiableOn_unoffsetLogIntegral_Ioi.continuousOn

/-! ### Behaviour as `x → 0⁺` -/

/-- The integrand `log t * exp (-t)` is integrable on `(0, ∞)`. -/
theorem integrableOn_Ioi_log_mul_exp_neg :
    IntegrableOn (fun t : ℝ ↦ Real.log t * Real.exp (-t)) (Ioi 0) := by
  have h01 : IntegrableOn (fun t : ℝ ↦ Real.log t * Real.exp (-t)) (Ioc 0 1) := by
    have hrpow : IntegrableOn (fun t : ℝ ↦ Real.sqrt 2 * t ^ (-(1 / 2 : ℝ))) (Ioc 0 1) :=
      ((intervalIntegral.intervalIntegrable_rpow'
        (by norm_num : (-1 : ℝ) < -(1 / 2))).1).const_mul _
    refine hrpow.mono' ?_ ?_
    · exact (Real.measurable_log.mul
        (Real.continuous_exp.comp continuous_neg).measurable).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := ht.1
      have hlog : |Real.log t| = -Real.log t := abs_of_nonpos (Real.log_nonpos ht0.le ht.2)
      have h1 : -Real.log t ≤ Real.sqrt (2 / t) := Real.neg_log_le_sqrt_two_div ht0.le
      have h2 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht0.le)
      rw [Real.norm_eq_abs, abs_mul, hlog, abs_of_pos (Real.exp_pos _)]
      calc -Real.log t * Real.exp (-t)
          ≤ Real.sqrt (2 / t) * 1 := mul_le_mul h1 h2 (Real.exp_pos _).le (Real.sqrt_nonneg _)
        _ = Real.sqrt 2 * t ^ (-(1 / 2 : ℝ)) := by
            rw [mul_one, Real.sqrt_div (by positivity), Real.rpow_neg ht0.le,
              ← Real.sqrt_eq_rpow, div_eq_mul_inv]
  have h1inf : IntegrableOn (fun t : ℝ ↦ Real.log t * Real.exp (-t)) (Ioi 1) := by
    have hgamma : IntegrableOn (fun t : ℝ ↦ Real.exp (-t) * t ^ ((2 : ℝ) - 1)) (Ioi 0) :=
      Real.GammaIntegral_convergent (by norm_num : (0 : ℝ) < 2)
    have htail : IntegrableOn (fun t : ℝ ↦ Real.exp (-t) * t) (Ioi 1) := by
      refine (hgamma.mono_set (Ioi_subset_Ioi zero_le_one)).congr_fun
        (fun t _ ↦ ?_) measurableSet_Ioi
      norm_num
    refine htail.mono' ?_ ?_
    · exact (Real.measurable_log.mul
        (Real.continuous_exp.comp continuous_neg).measurable).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := zero_lt_one.trans ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.log_pos ht), abs_of_pos (Real.exp_pos _)]
      calc Real.log t * Real.exp (-t)
          ≤ t * Real.exp (-t) :=
            mul_le_mul_of_nonneg_right (Real.log_le_self ht0.le) (Real.exp_pos _).le
        _ = Real.exp (-t) * t := mul_comm _ _
  simpa only [Ioc_union_Ioi_eq_Ioi zero_le_one] using h01.union h1inf

/-- Integration by parts on `[0, z]` relating `∫ t in 0..z, (1 - e^{-t}) / t` and
`∫ t in 0..z, log t * e^{-t}`. -/
theorem integral_one_sub_exp_neg_div_eq_sub_integral {z : ℝ} (hz : 0 ≤ z) :
    ∫ t in (0 : ℝ)..z, (1 - Real.exp (-t)) / t =
      (1 - Real.exp (-z)) * Real.log z - ∫ t in (0 : ℝ)..z, Real.log t * Real.exp (-t) := by
  rcases hz.eq_or_lt with rfl | hz_pos
  · simp
  let f (t : ℝ) : ℝ := (1 - Real.exp (-t)) * Real.log t
  let f' (t : ℝ) : ℝ := Real.exp (-t) * Real.log t + (1 - Real.exp (-t)) / t
  have hderiv : ∀ t ∈ Ioo 0 z, HasDerivAt f (f' t) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ ↦ 1 - Real.exp (-s)) (Real.exp (-t)) t := by
      simpa using ((hasDerivAt_neg t).exp).const_sub 1
    have h2 : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht.1.ne'
    refine (h1.mul h2).congr_deriv ?_
    simp [f', div_eq_mul_inv]
  have hint1 : IntervalIntegrable (fun t : ℝ ↦ Real.exp (-t) * Real.log t) volume 0 z := by
    have hcongr :
        (fun t : ℝ ↦ Real.exp (-t) * Real.log t) = fun t ↦ Real.log t * Real.exp (-t) := by
      ext t; ring
    rw [hcongr, intervalIntegrable_iff_integrableOn_Ioc_of_le hz]
    exact integrableOn_Ioi_log_mul_exp_neg.mono_set Ioc_subset_Ioi_self
  have hint2 : IntervalIntegrable (fun t : ℝ ↦ (1 - Real.exp (-t)) / t) volume 0 z := by
    let g : ℝ → ℝ := fun t ↦ if t = 0 then 1 else (1 - Real.exp (-t)) / t
    have hg : Continuous g := by
      have heq : g = fun t ↦ if -t = 0 then (1 : ℝ) else (Real.exp (-t) - 1) / (-t) := by
        ext t
        by_cases ht : t = 0
        · simp [g, ht]
        · have hnt : -t ≠ 0 := neg_ne_zero.mpr ht
          simp only [g, ht, ↓reduceIte, hnt]
          ring
      rw [heq]
      exact continuous_exp_sub_one_div.comp continuous_neg
    refine (hg.intervalIntegrable 0 z).congr_ae ?_
    have hne : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := ae_iff.mpr (by simp)
    filter_upwards [ae_restrict_of_ae hne] with t ht
    dsimp only [g]
    simp [ht]
  have hlim0 : Tendsto f (𝓝[>] 0) (𝓝 0) := by
    have hratio : Tendsto (fun t : ℝ ↦ (1 - Real.exp (-t)) / t) (𝓝[>] 0) (𝓝 1) := by
      have h1 := ((Real.tendsto_exp_mul_sub_one_div (-1)).mono_left
        (nhdsWithin_mono _ (fun _ ht ↦ ne_of_gt (mem_Ioi.mp ht)))).neg
      rw [neg_neg] at h1
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t _
      rw [neg_one_mul]
      ring
    have htlog : Tendsto (fun t : ℝ ↦ t * Real.log t) (𝓝[>] 0) (𝓝 0) := by
      simpa [mul_comm] using tendsto_log_mul_rpow_nhdsGT_zero one_pos
    have hprod := hratio.mul htlog
    rw [one_mul] at hprod
    refine hprod.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (t : ℝ) ≠ 0 := ne_of_gt (mem_Ioi.mp ht)
    simp only [f]
    field_simp [ht0]
  have hlimz : Tendsto f (𝓝[<] z) (𝓝 ((1 - Real.exp (-z)) * Real.log z)) := by
    have hcont : ContinuousAt f z := by fun_prop (disch := exact hz_pos.ne')
    exact hcont.continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hz_pos hderiv
    (hint1.add hint2) hlim0 hlimz
  rw [intervalIntegral.integral_add hint1 hint2, sub_zero] at hFTC
  have hcomm : (∫ t in (0 : ℝ)..z, Real.exp (-t) * Real.log t) =
      ∫ t in (0 : ℝ)..z, Real.log t * Real.exp (-t) := by
    refine intervalIntegral.integral_congr fun t _ ↦ mul_comm _ _
  linarith

/-- For `0 < x < 1`, `li x = γ + x log (-log x) + ∫ t in 0..(-log x), log t * e^{-t}`. -/
theorem unoffsetLogIntegral_of_Ioo {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    unoffsetLogIntegral x = Real.eulerMascheroniConstant + x * Real.log (-Real.log x) +
      ∫ t in (0 : ℝ)..(-Real.log x), Real.log t * Real.exp (-t) := by
  set z : ℝ := -Real.log x
  have hz : 0 < z := neg_pos.mpr (Real.log_neg hx₀ hx₁)
  have htsum := integral_one_sub_exp_neg_div_eq z
  have hibp := integral_one_sub_exp_neg_div_eq_sub_integral hz.le
  have hexp : Real.exp (-z) = x := by simp [z, Real.exp_log hx₀]
  rw [unoffsetLogIntegral_def]
  have hlogabs : Real.log (Real.log x) = Real.log z := by
    rw [← Real.log_neg_eq_log]
  rw [hlogabs, show Real.log x = -z by simp [z], ← neg_neg (∑' n : ℕ, _), ← htsum, hibp, hexp]
  ring

/-- `li x → 0` as `x → 0⁺`. -/
theorem tendsto_unoffsetLogIntegral_nhdsGT_zero :
    Tendsto unoffsetLogIntegral (𝓝[>] 0) (𝓝 0) := by
  have hz_atTop : Tendsto (fun x : ℝ ↦ -Real.log x) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hxlog : Tendsto (fun z : ℝ ↦ Real.exp (-z) * Real.log z) atTop (𝓝 0) := by
    have hpoly : Tendsto (fun z : ℝ ↦ z * Real.exp (-z)) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    refine squeeze_zero' (g := fun z : ℝ ↦ z * Real.exp (-z)) ?_ ?_ hpoly
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
      exact mul_nonneg (Real.exp_pos _).le (Real.log_nonneg hz)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (Real.log_le_self (by positivity)) (Real.exp_pos _).le
  have hint : Tendsto (fun z : ℝ ↦ ∫ t in (0 : ℝ)..z, Real.log t * Real.exp (-t)) atTop
      (𝓝 (-Real.eulerMascheroniConstant)) := by
    rw [Real.eulerMascheroniConstant_eq_neg_integral_log, neg_neg]
    exact intervalIntegral_tendsto_integral_Ioi 0 integrableOn_Ioi_log_mul_exp_neg tendsto_id
  have hsum : Tendsto (fun x : ℝ ↦ Real.eulerMascheroniConstant +
      x * Real.log (-Real.log x) + ∫ t in (0 : ℝ)..(-Real.log x), Real.log t * Real.exp (-t))
      (𝓝[>] 0) (𝓝 0) := by
    have hxexp : Tendsto (fun x : ℝ ↦ x * Real.log (-Real.log x)) (𝓝[>] 0) (𝓝 0) := by
      refine (hxlog.comp hz_atTop).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      simp [Real.exp_log hx]
    have h0 := (tendsto_const_nhds (x := Real.eulerMascheroniConstant)).add hxexp
    have h1 := h0.add (hint.comp hz_atTop)
    simpa [add_assoc] using h1
  refine hsum.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
  exact (unoffsetLogIntegral_of_Ioo hx.1 hx.2).symm

/-! ### Principal value and comparison with the offset logarithmic integral -/

/-- `(log t)⁻¹` is interval integrable on `[0, x]` whenever `0 ≤ x < 1`. -/
theorem intervalIntegrable_inv_log_of_Ico {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x < 1) :
    IntervalIntegrable (fun t : ℝ ↦ (Real.log t)⁻¹) volume 0 x := by
  refine ContinuousOn.intervalIntegrable_of_Icc hx₀ fun t ht ↦ ?_
  rcases ht.1.eq_or_lt with rfl | ht0
  · exact Real.continuousAt_inv_log_zero.continuousWithinAt
  · have hlog : Real.log t ≠ 0 := (Real.log_neg ht0 (ht.2.trans_lt hx₁)).ne
    have hcont : ContinuousAt (fun s : ℝ ↦ (Real.log s)⁻¹) t :=
      (Real.continuousAt_log ht0.ne').inv₀ hlog
    exact hcont.continuousWithinAt

/-- For `0 < x < 1`, `li x = ∫ t in 0..x, (log t)⁻¹`. -/
theorem unoffsetLogIntegral_eq_integral {x : ℝ} (hx₀ : 0 < x) (hx₁ : x < 1) :
    unoffsetLogIntegral x = ∫ t in (0 : ℝ)..x, (Real.log t)⁻¹ := by
  have hderiv : ∀ t ∈ Ioo 0 x, HasDerivAt unoffsetLogIntegral (Real.log t)⁻¹ t :=
    fun t ht ↦ hasDerivAt_unoffsetLogIntegral ht.1 (ht.2.trans hx₁).ne
  have hint := intervalIntegrable_inv_log_of_Ico hx₀.le hx₁
  have hlimx : Tendsto unoffsetLogIntegral (𝓝[<] x) (𝓝 (unoffsetLogIntegral x)) :=
    (hasDerivAt_unoffsetLogIntegral hx₀ hx₁.ne).continuousAt.continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hx₀ hderiv hint
    tendsto_unoffsetLogIntegral_nhdsGT_zero hlimx
  linarith

/-- Symmetric cancellation of the logarithmic singularity at `1`:
`li (1 + ε) - li (1 - ε) → 0` as `ε → 0⁺`. -/
theorem tendsto_unoffsetLogIntegral_add_sub_sub :
    Tendsto (fun ε : ℝ ↦ unoffsetLogIntegral (1 + ε) - unoffsetLogIntegral (1 - ε))
      (𝓝[>] 0) (𝓝 0) := by
  let S (y : ℝ) : ℝ := ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ))
  have hS_cont : ContinuousAt S 0 := (hasDerivAt_tsum_pow_div_mul_factorial 0).continuousAt
  have hlog_add : Tendsto (fun ε : ℝ ↦ Real.log (1 + ε)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : ContinuousAt (fun ε : ℝ ↦ Real.log (1 + ε)) 0 := by fun_prop (disch := norm_num)
    simpa using h1.tendsto.mono_left nhdsWithin_le_nhds
  have hlog_sub : Tendsto (fun ε : ℝ ↦ Real.log (1 - ε)) (𝓝[>] 0) (𝓝 0) := by
    have h1 : ContinuousAt (fun ε : ℝ ↦ Real.log (1 - ε)) 0 := by fun_prop (disch := norm_num)
    simpa using h1.tendsto.mono_left nhdsWithin_le_nhds
  have hS_diff : Tendsto (fun ε : ℝ ↦ S (Real.log (1 + ε)) - S (Real.log (1 - ε)))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using (hS_cont.tendsto.comp hlog_add).sub (hS_cont.tendsto.comp hlog_sub)
  have hslope_add : Tendsto (fun ε : ℝ ↦ Real.log (1 + ε) / ε) (𝓝[>] 0) (𝓝 1) := by
    have hd : HasDerivAt (fun ε : ℝ ↦ Real.log (1 + ε)) 1 0 := by
      have hlin : HasDerivAt (fun ε : ℝ ↦ (1 : ℝ) + ε) 1 0 :=
        (hasDerivAt_id (0 : ℝ)).const_add 1
      exact ((Real.hasDerivAt_log (by norm_num : (1 : ℝ) + 0 ≠ 0)).comp 0 hlin).congr_deriv
        (by norm_num)
    simpa [div_eq_inv_mul] using
      hd.tendsto_slope_zero.mono_left (nhdsWithin_mono _ fun _ h ↦ ne_of_gt h)
  have hslope_sub : Tendsto (fun ε : ℝ ↦ -Real.log (1 - ε) / ε) (𝓝[>] 0) (𝓝 1) := by
    have hd : HasDerivAt (fun ε : ℝ ↦ -Real.log (1 - ε)) 1 0 := by
      have hlin : HasDerivAt (fun ε : ℝ ↦ (1 : ℝ) - ε) (-1) 0 :=
        (hasDerivAt_id (0 : ℝ)).const_sub 1
      exact (((Real.hasDerivAt_log (by norm_num : (1 : ℝ) - 0 ≠ 0)).comp 0 hlin).neg).congr_deriv
        (by norm_num)
    simpa [div_eq_inv_mul] using
      hd.tendsto_slope_zero.mono_left (nhdsWithin_mono _ fun _ h ↦ ne_of_gt h)
  have hratio : Tendsto (fun ε : ℝ ↦ Real.log (1 + ε) / (-Real.log (1 - ε))) (𝓝[>] 0) (𝓝 1) := by
    have hq := hslope_add.div hslope_sub one_ne_zero
    rw [div_one] at hq
    refine hq.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
    have hε0 : ε ≠ 0 := hε.1.ne'
    have hneg : -Real.log (1 - ε) ≠ 0 :=
      (neg_pos.mpr (Real.log_neg (by linarith [hε.2]) (by linarith [hε.1]))).ne'
    dsimp only [Pi.div_apply]
    field_simp [hε0, hneg]
  have hlogratio : Tendsto (fun ε : ℝ ↦ Real.log (Real.log (1 + ε) / (-Real.log (1 - ε))))
      (𝓝[>] 0) (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuousAt_log one_ne_zero).tendsto.comp hratio
  have hsum := hlogratio.add hS_diff
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
  have hp : 0 < Real.log (1 + ε) := Real.log_pos (by linarith [hε.1])
  have hn : 0 < -Real.log (1 - ε) :=
    neg_pos.mpr (Real.log_neg (by linarith [hε.2]) (by linarith [hε.1]))
  rw [unoffsetLogIntegral_def, unoffsetLogIntegral_def]
  have hld : Real.log (Real.log (1 + ε)) - Real.log (Real.log (1 - ε)) =
      Real.log (Real.log (1 + ε) / (-Real.log (1 - ε))) := by
    rw [Real.log_div hp.ne' hn.ne', Real.log_neg_eq_log]
  dsimp only [S]
  linarith

/-- **Cauchy principal value for `li x`** (`x > 1`):
`lim_{ε → 0⁺} (∫ t in 0..(1 - ε), (log t)⁻¹ + ∫ t in (1 + ε)..x, (log t)⁻¹) = li x`. -/
theorem tendsto_principalValue_inv_log {x : ℝ} (hx : 1 < x) :
    Tendsto (fun ε : ℝ ↦ (∫ t in (0 : ℝ)..(1 - ε), (Real.log t)⁻¹) +
        ∫ t in (1 + ε)..x, (Real.log t)⁻¹)
      (𝓝[>] 0) (𝓝 (unoffsetLogIntegral x)) := by
  have hsub :=
    (tendsto_const_nhds (x := unoffsetLogIntegral x)).sub tendsto_unoffsetLogIntegral_add_sub_sub
  rw [sub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min zero_lt_one (sub_pos.mpr hx))] with ε hε
  have hε1 : ε < 1 := hε.2.trans_le (min_le_left _ _)
  have hεx : 1 + ε < x := by linarith [hε.2.trans_le (min_le_right _ _)]
  have hleft : ∫ t in (0 : ℝ)..(1 - ε), (Real.log t)⁻¹ = unoffsetLogIntegral (1 - ε) :=
    (unoffsetLogIntegral_eq_integral (by linarith [hε1]) (by linarith [hε.1])).symm
  have hright : ∫ t in (1 + ε)..x, (Real.log t)⁻¹ =
      unoffsetLogIntegral x - unoffsetLogIntegral (1 + ε) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ ?_
    · intro t ht
      rw [uIcc_of_le hεx.le] at ht
      exact hasDerivAt_unoffsetLogIntegral (by linarith [ht.1, hε.1]) (by linarith [ht.1, hε.1])
    · simpa only [pow_one] using intervalIntegrable_inv_log_pow 1 (by linarith [hε.1]) hx
  rw [hleft, hright]
  ring

/-- **The offset relation**: `Li x = li x - li 2` for every `x > 1`. -/
theorem logIntegral_eq_unoffsetLogIntegral_sub {x : ℝ} (hx : 1 < x) :
    logIntegral x = unoffsetLogIntegral x - unoffsetLogIntegral 2 := by
  rw [logIntegral_def]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ ?_
  · intro t ht
    have ht1 : 1 < t := ordConnected_Ioi.uIcc_subset one_lt_two hx ht
    exact hasDerivAt_unoffsetLogIntegral (zero_lt_one.trans ht1) ht1.ne'
  · simpa only [pow_one] using intervalIntegrable_inv_log_pow 1 one_lt_two hx

/-- For every `x > 1`, `li x = Li x + li 2`. -/
theorem unoffsetLogIntegral_eq_logIntegral_add {x : ℝ} (hx : 1 < x) :
    unoffsetLogIntegral x = logIntegral x + unoffsetLogIntegral 2 := by
  linarith [logIntegral_eq_unoffsetLogIntegral_sub hx]

/-! ### Monotonicity, limits, and Soldner's constant -/

/-- `li` is strictly decreasing on `(0, 1)`. -/
theorem strictAntiOn_unoffsetLogIntegral_Ioo : StrictAntiOn unoffsetLogIntegral (Ioo 0 1) := by
  refine strictAntiOn_of_hasDerivWithinAt_neg (f' := fun t ↦ (Real.log t)⁻¹) (convex_Ioo 0 1)
    continuousOn_unoffsetLogIntegral_Ioo (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · rw [interior_Ioo] at hx
    exact (hasDerivAt_unoffsetLogIntegral hx.1 hx.2.ne).hasDerivWithinAt
  · rw [interior_Ioo] at hx
    exact inv_lt_zero.mpr (Real.log_neg hx.1 hx.2)

/-- For every `x ∈ (0, 1)`, `li x < 0`. -/
theorem unoffsetLogIntegral_neg_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo 0 1) :
    unoffsetLogIntegral x < 0 := by
  have hx2 : x / 2 ∈ Ioo (0 : ℝ) 1 := ⟨half_pos hx.1, by linarith [hx.2]⟩
  have hlt : unoffsetLogIntegral x < unoffsetLogIntegral (x / 2) :=
    strictAntiOn_unoffsetLogIntegral_Ioo hx2 hx (by linarith [hx.1])
  have hle : unoffsetLogIntegral (x / 2) ≤ 0 := by
    refine ge_of_tendsto tendsto_unoffsetLogIntegral_nhdsGT_zero ?_
    filter_upwards [Ioo_mem_nhdsGT (half_pos hx.1)] with y hy
    exact (strictAntiOn_unoffsetLogIntegral_Ioo ⟨hy.1, by linarith [hy.2, hx.2]⟩ hx2 hy.2).le
  exact hlt.trans_le hle

/-- `li` is strictly increasing on `(1, ∞)`. -/
theorem strictMonoOn_unoffsetLogIntegral_Ioi : StrictMonoOn unoffsetLogIntegral (Ioi 1) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (f' := fun t ↦ (Real.log t)⁻¹) (convex_Ioi 1)
    continuousOn_unoffsetLogIntegral_Ioi (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · rw [interior_Ioi] at hx
    exact (hasDerivAt_unoffsetLogIntegral (zero_lt_one.trans hx) hx.ne').hasDerivWithinAt
  · rw [interior_Ioi] at hx
    exact inv_pos.mpr (Real.log_pos hx)

/-- `li x → -∞` as `x → 1` (`x ≠ 1`). -/
theorem tendsto_unoffsetLogIntegral_nhdsNE_one :
    Tendsto unoffsetLogIntegral (𝓝[≠] 1) atBot := by
  let S (y : ℝ) : ℝ := ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ))
  have hlog : Tendsto Real.log (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using (Real.continuousAt_log one_ne_zero).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
        (eventually_gt_nhds zero_lt_one)] with x hx hx0
      exact Real.log_ne_zero_of_pos_of_ne_one hx0 hx
  have hloglog : Tendsto (fun x : ℝ ↦ Real.log (Real.log x)) (𝓝[≠] 1) atBot :=
    Real.tendsto_log_nhdsNE_zero.comp hlog
  have hS : Tendsto (fun x : ℝ ↦ S (Real.log x)) (𝓝[≠] 1) (𝓝 0) := by
    have hS0 : ContinuousAt S 0 := (hasDerivAt_tsum_pow_div_mul_factorial 0).continuousAt
    simpa [S, Function.comp_def] using hS0.tendsto.comp (hlog.mono_right nhdsWithin_le_nhds)
  have hsum : Tendsto (fun x : ℝ ↦ (Real.eulerMascheroniConstant + S (Real.log x)) +
      Real.log (Real.log x)) (𝓝[≠] 1) atBot :=
    Tendsto.add_atBot ((tendsto_const_nhds (x := Real.eulerMascheroniConstant)).add hS) hloglog
  refine hsum.congr fun x ↦ ?_
  rw [unoffsetLogIntegral_def]
  dsimp only [S]
  ring

/-- `li x → -∞` as `x → 1⁻`. -/
theorem tendsto_unoffsetLogIntegral_nhdsLT_one :
    Tendsto unoffsetLogIntegral (𝓝[<] 1) atBot :=
  tendsto_unoffsetLogIntegral_nhdsNE_one.mono_left (nhdsWithin_mono _ fun _ hx ↦ hx.ne)

/-- `li x → -∞` as `x → 1⁺`. -/
theorem tendsto_unoffsetLogIntegral_nhdsGT_one :
    Tendsto unoffsetLogIntegral (𝓝[>] 1) atBot :=
  tendsto_unoffsetLogIntegral_nhdsNE_one.mono_left (nhdsWithin_mono _ fun _ hx ↦ hx.ne')

/-- `li x → +∞` as `x → ∞`. -/
theorem tendsto_unoffsetLogIntegral_atTop :
    Tendsto unoffsetLogIntegral atTop atTop := by
  have hLi : Tendsto logIntegral atTop atTop := by
    have hhalf : Tendsto (fun x : ℝ ↦ (1 / 2 : ℝ) * (x / Real.log x)) atTop atTop :=
      tendsto_div_log_atTop.const_mul_atTop (by norm_num)
    refine tendsto_atTop_mono' atTop ?_ hhalf
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    calc (1 / 2 : ℝ) * (x / Real.log x)
        = (x / 2) / Real.log x := by ring
      _ ≤ (x - 2) / Real.log x := by gcongr; linarith
      _ ≤ logIntegral x := le_logIntegral (by linarith)
  have hadd : Tendsto (fun x : ℝ ↦ logIntegral x + unoffsetLogIntegral 2) atTop atTop :=
    hLi.atTop_add tendsto_const_nhds
  refine hadd.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact (unoffsetLogIntegral_eq_logIntegral_add hx).symm

/-- **Soldner's constant**: `li` has a unique zero in `(1, ∞)`. -/
theorem existsUnique_unoffsetLogIntegral_eq_zero :
    ∃! μ ∈ Ioi (1 : ℝ), unoffsetLogIntegral μ = 0 := by
  obtain ⟨a, ha1, ha0⟩ : ∃ a ∈ Ioi (1 : ℝ), unoffsetLogIntegral a < 0 := by
    have hev := (tendsto_unoffsetLogIntegral_nhdsGT_one.eventually (eventually_lt_atBot 0)).and
      self_mem_nhdsWithin
    obtain ⟨a, ha0, ha1⟩ := hev.exists
    exact ⟨a, ha1, ha0⟩
  obtain ⟨b, hb_gt, hb0⟩ : ∃ b > a, 0 < unoffsetLogIntegral b := by
    have hev := (tendsto_unoffsetLogIntegral_atTop.eventually (eventually_gt_atTop 0)).and
      (eventually_gt_atTop a)
    obtain ⟨b, hb0, hba⟩ := hev.exists
    exact ⟨b, hba, hb0⟩
  have hab : a ≤ b := hb_gt.le
  have hcont : ContinuousOn unoffsetLogIntegral (Icc a b) :=
    continuousOn_unoffsetLogIntegral_Ioi.mono (Icc_subset_Ioi_iff hab |>.mpr ha1)
  obtain ⟨μ, hμ, hμ0⟩ := intermediate_value_Icc hab hcont (mem_Icc.mpr ⟨ha0.le, hb0.le⟩)
  refine ⟨μ, ⟨ha1.trans_le hμ.1, hμ0⟩, fun ν hν ↦ ?_⟩
  rcases lt_trichotomy ν μ with hlt | rfl | hgt
  · exact absurd (strictMonoOn_unoffsetLogIntegral_Ioi hν.1 (ha1.trans_le hμ.1) hlt)
      (by linarith [hν.2, hμ0])
  · rfl
  · exact absurd (strictMonoOn_unoffsetLogIntegral_Ioi (ha1.trans_le hμ.1) hν.1 hgt)
      (by linarith [hν.2, hμ0])

/-! ### Asymptotic expansion -/

/-- Exact `n`-step integration by parts of `Li x` from base point `2`. -/
private theorem logIntegral_eq_sub_add_integral (n : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    logIntegral x =
      (x / Real.log x) * (∑ k ∈ Finset.range n, (k ! : ℝ) / Real.log x ^ k) -
        (2 / Real.log 2) * (∑ k ∈ Finset.range n, (k ! : ℝ) / Real.log 2 ^ k) +
        (n ! : ℝ) * ∫ t in (2 : ℝ)..x, (Real.log t ^ (n + 1))⁻¹ := by
  have hx1 : 1 < x := one_lt_two.trans_le hx
  induction n with
  | zero =>
      simp [logIntegral_def]
  | succ n ih =>
      have hibp := integral_inv_log_pow_eq_sub_add (n + 1) one_lt_two hx1
      have hlogx : Real.log x ≠ 0 := (Real.log_pos hx1).ne'
      have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
      rw [ih, Finset.sum_range_succ, Finset.sum_range_succ, hibp]
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hpowx : (x / Real.log x) * ((n ! : ℝ) / Real.log x ^ n) =
          (n ! : ℝ) * (x / Real.log x ^ (n + 1)) := by
        rw [pow_succ']
        field_simp [hlogx]
      have hpow2 : (2 / Real.log 2) * ((n ! : ℝ) / Real.log 2 ^ n) =
          (n ! : ℝ) * (2 / Real.log 2 ^ (n + 1)) := by
        rw [pow_succ']
        field_simp [hlog2]
      rw [mul_add, mul_add]
      linarith

/-- For every `m ≥ 1`, `∫ t in 2..x, (log t ^ m)⁻¹ = O(x / log x ^ m)` as `x → ∞`. -/
private theorem isBigO_integral_inv_log_pow_succ (m : ℕ) :
    (fun x : ℝ ↦ ∫ t in (2 : ℝ)..x, (Real.log t ^ (m + 1))⁻¹) =O[atTop]
      fun x : ℝ ↦ x / Real.log x ^ (m + 1) := by
  have hsqrt_little : (fun x : ℝ ↦ √x) =o[atTop] fun x : ℝ ↦ x / Real.log x ^ (m + 1) := by
    have hmpos : (0 : ℝ) < 1 / (2 * ((m : ℝ) + 1)) := by positivity
    have hlog : (fun x : ℝ ↦ Real.log x) =o[atTop] fun x : ℝ ↦ x ^ (1 / (2 * ((m : ℝ) + 1))) :=
      isLittleO_log_rpow_atTop hmpos
    have hpow := hlog.pow (Nat.succ_pos m)
    have hlim : Tendsto (fun x : ℝ ↦ Real.log x ^ (m + 1) / √x) atTop (𝓝 0) := by
      refine hpow.tendsto_div_nhds_zero.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (x ^ _) m.succ, ← Real.rpow_mul hx.le]
      congr 2
      push_cast
      field_simp
    refine (isLittleO_iff_tendsto' ?_).mpr ?_
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx h0
      exact absurd h0 (div_pos (zero_lt_one.trans hx) (pow_pos (Real.log_pos hx) _)).ne'
    · refine hlim.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [div_div_eq_mul_div]
      have hsqne : √x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
      field_simp [hsqne]
      rw [Real.sq_sqrt hx.le]
  have hsqrt_big : (fun x : ℝ ↦ √x / Real.log 2 ^ (m + 1)) =O[atTop]
      fun x : ℝ ↦ x / Real.log x ^ (m + 1) :=
    (hsqrt_little.isBigO.const_mul_left (Real.log 2 ^ (m + 1))⁻¹).congr_left fun x ↦ by
      simp [div_eq_mul_inv, mul_comm]
  have hmain_big : (fun x : ℝ ↦ (2 : ℝ) ^ (m + 1) * x / Real.log x ^ (m + 1)) =O[atTop]
      fun x : ℝ ↦ x / Real.log x ^ (m + 1) := by
    refine (isBigO_refl (fun x : ℝ ↦ x / Real.log x ^ (m + 1)) atTop).const_mul_left
      ((2 : ℝ) ^ (m + 1)) |>.congr_left fun x ↦ ?_
    simp [mul_div_assoc]
  have hle_majorant : (fun x : ℝ ↦ ∫ t in (2 : ℝ)..x, (Real.log t ^ (m + 1))⁻¹) =O[atTop]
      fun x : ℝ ↦ √x / Real.log 2 ^ (m + 1) + (2 : ℝ) ^ (m + 1) * x / Real.log x ^ (m + 1) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have h2sq : (2 : ℝ) ≤ √x := by
      have h4 : √(4 : ℝ) ≤ √x := Real.sqrt_le_sqrt hx
      rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at h4
    have hsqx : √x ≤ x := by rw [Real.sqrt_le_self_iff]; exact Or.inr (by linarith)
    have hsplit : (∫ t in (2 : ℝ)..x, (Real.log t ^ (m + 1))⁻¹) =
        (∫ t in (2 : ℝ)..√x, (Real.log t ^ (m + 1))⁻¹) +
          ∫ t in √x..x, (Real.log t ^ (m + 1))⁻¹ :=
      (intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_inv_log_pow (m + 1) one_lt_two (by linarith))
        (intervalIntegrable_inv_log_pow (m + 1) (by linarith) (by linarith))).symm
    have hb1 : (∫ t in (2 : ℝ)..√x, (Real.log t ^ (m + 1))⁻¹) ≤ √x / Real.log 2 ^ (m + 1) := by
      refine (integral_inv_log_pow_le (m + 1) one_lt_two h2sq).trans ?_
      gcongr
      linarith
    have hb2 : (∫ t in √x..x, (Real.log t ^ (m + 1))⁻¹) ≤
        (2 : ℝ) ^ (m + 1) * x / Real.log x ^ (m + 1) := by
      refine (integral_inv_log_pow_le (m + 1) (by linarith) hsqx).trans ?_
      have hlogsq : Real.log √x = Real.log x / 2 := Real.log_sqrt hx0.le
      rw [hlogsq, div_pow, div_div_eq_mul_div, mul_comm (x - √x),
        div_le_div_iff_of_pos_right (pow_pos (Real.log_pos (by linarith)) _)]
      have hle : x - √x ≤ x := sub_le_self x (Real.sqrt_nonneg x)
      gcongr
    have hnn : 0 ≤ ∫ t in (2 : ℝ)..x, (Real.log t ^ (m + 1))⁻¹ :=
      integral_inv_log_pow_nonneg (m + 1) one_lt_two (by linarith)
    have hmaj_nn :
        0 ≤ √x / Real.log 2 ^ (m + 1) + (2 : ℝ) ^ (m + 1) * x / Real.log x ^ (m + 1) := by
      have : 0 < Real.log 2 := Real.log_pos one_lt_two
      have : 0 < Real.log x := Real.log_pos (by linarith)
      positivity
    rw [one_mul, Real.norm_of_nonneg hnn, Real.norm_of_nonneg hmaj_nn, hsplit]
    exact add_le_add hb1 hb2
  exact hle_majorant.trans (hsqrt_big.add hmain_big)

/-- **Asymptotic expansion of `li x`**: for every `n : ℕ`,
`li x = (x / log x) * ∑ k < n, k! / (log x) ^ k + O(x / (log x) ^ (n + 1))` as `x → ∞`. -/
theorem unoffsetLogIntegral_sub_sum_isBigO (n : ℕ) :
    (fun x : ℝ ↦ unoffsetLogIntegral x -
        (x / Real.log x) * ∑ k ∈ Finset.range n, (k ! : ℝ) / Real.log x ^ k) =O[atTop]
      fun x : ℝ ↦ x / Real.log x ^ (n + 1) := by
  let C : ℝ := unoffsetLogIntegral 2 -
    (2 / Real.log 2) * ∑ k ∈ Finset.range n, (k ! : ℝ) / Real.log 2 ^ k
  have hconst_tendsto : Tendsto (fun x : ℝ ↦ Real.log x ^ (n + 1) / x) atTop (𝓝 0) := by
    have hnpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hlog : (fun x : ℝ ↦ Real.log x) =o[atTop] fun x : ℝ ↦ x ^ (1 / ((n : ℝ) + 1)) :=
      isLittleO_log_rpow_atTop hnpos
    refine (hlog.pow (Nat.succ_pos n)).tendsto_div_nhds_zero.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_natCast (x ^ _) n.succ, ← Real.rpow_mul hx.le]
    have h1 : (1 / ((n : ℝ) + 1)) * (n.succ : ℝ) = 1 := by
      push_cast
      field_simp
    rw [h1, Real.rpow_one]
  have hconst : (fun _ : ℝ ↦ C) =O[atTop] fun x : ℝ ↦ x / Real.log x ^ (n + 1) := by
    refine (isLittleO_iff_tendsto' ?_).mpr ?_ |>.isBigO
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx h0
      exact absurd h0 (div_pos (zero_lt_one.trans hx) (pow_pos (Real.log_pos hx) _)).ne'
    · have hmul : Tendsto (fun x : ℝ ↦ C * (Real.log x ^ (n + 1) / x)) atTop (𝓝 0) := by
        simpa using hconst_tendsto.const_mul C
      refine hmul.congr' ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x _
      rw [div_div_eq_mul_div]
      ring
  have hrem : (fun x : ℝ ↦ (n ! : ℝ) * ∫ t in (2 : ℝ)..x, (Real.log t ^ (n + 1))⁻¹) =O[atTop]
      fun x : ℝ ↦ x / Real.log x ^ (n + 1) :=
    (isBigO_integral_inv_log_pow_succ n).const_mul_left (n ! : ℝ)
  refine (hconst.add hrem).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hx1 : 1 < x := one_lt_two.trans_le hx
  rw [unoffsetLogIntegral_eq_logIntegral_add hx1, logIntegral_eq_sub_add_integral n hx]
  dsimp only [C]
  ring

/-- `li x ~ Li x` as `x → ∞`. -/
theorem unoffsetLogIntegral_isEquivalent_logIntegral :
    unoffsetLogIntegral ~[atTop] logIntegral := by
  have hdiff : (fun x : ℝ ↦ unoffsetLogIntegral x - logIntegral x) =o[atTop] logIntegral := by
    have hconst : (fun _ : ℝ ↦ unoffsetLogIntegral 2) =o[atTop] fun x : ℝ ↦ x / Real.log x :=
      isLittleO_const_div_log (unoffsetLogIntegral 2)
    have hli := hconst.trans_isEquivalent logIntegral_isEquivalent_div_log.symm
    refine hli.congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [unoffsetLogIntegral_eq_logIntegral_add hx]
    ring
  exact hdiff.isEquivalent

/-- `li x ~ x / log x` as `x → ∞`. -/
theorem unoffsetLogIntegral_isEquivalent_div_log :
    unoffsetLogIntegral ~[atTop] fun x : ℝ ↦ x / Real.log x :=
  unoffsetLogIntegral_isEquivalent_logIntegral.trans logIntegral_isEquivalent_div_log

end TauCeti.Real
