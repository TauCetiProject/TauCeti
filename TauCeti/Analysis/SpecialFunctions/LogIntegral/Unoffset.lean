/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import TauCeti.Analysis.SpecialFunctions.LogIntegral.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
# The unoffset logarithmic integral

This file defines the unoffset logarithmic integral

```text
li x = γ + log |log x| + ∑' n : ℕ, (log x) ^ (n + 1) / ((n + 1) * (n + 1)!)
```

for real `x > 0`, `x ≠ 1` (the exponential integral `Ei` evaluated at `log x`; the value at
`x = 1` is junk). Unlike the offset logarithmic integral `TauCeti.Real.logIntegral` (`Li x`, with
`Li 2 = 0`), `li` cannot be defined on `(1, ∞)` by a plain interval integral from `0` to `x`
because `(log t)⁻¹` has a nonintegrable singularity at `t = 1`. Defining `li` by the globally
convergent series avoids that singularity and lets the Cauchy principal value and exponential
integral representations (proved in `TauCeti.Analysis.SpecialFunctions.LogIntegral.PrincipalValue`)
follow as theorems.

## Main declarations

* `TauCeti.Real.li` — the unoffset logarithmic integral, with `TauCeti.Real.li_def` and
  `TauCeti.Real.li_eq_add_log_abs`.
* `TauCeti.Real.integral_exp_sub_one_div_eq_tsum` — the entire-part integral
  `∫ u in 0..y, (exp u - 1) / u = ∑_{n ≥ 1} y^n / (n * n!)`.
* `TauCeti.Real.hasDerivAt_li` — `li' x = (log x)⁻¹` for `x > 0`, `x ≠ 1`.
* `TauCeti.Real.eulerMascheroniConstant_eq_integral_sub_integral` —
  `γ = ∫ t in 0..1, (1 - exp (-t)) / t - ∫ t in Ioi 1, exp (-t) / t`.
* `TauCeti.Real.tendsto_li_nhdsGT_zero` — `li x → 0` as `x → 0⁺`.
* `TauCeti.Real.logIntegral_eq_li_sub_li_two` — the offset identity `Li x = li x - li 2` for
  `x > 1`.
* `TauCeti.Real.strictAntiOn_li_Ioo`, `TauCeti.Real.li_neg`,
  `TauCeti.Real.strictMonoOn_li_Ioi`, `TauCeti.Real.tendsto_li_nhdsGT_one`,
  `TauCeti.Real.tendsto_li_nhdsLT_one`, `TauCeti.Real.tendsto_li_atTop`,
  `TauCeti.Real.li_pos_of_three_halves_le`, and `TauCeti.Real.existsUnique_li_eq_zero` —
  monotonicity, boundary limits, positivity for `x ≥ 3 / 2`, and Soldner's constant.

## References

* F. W. J. Olver et al., *NIST Digital Library of Mathematical Functions*, §6.2 (Exponential,
  Logarithmic, Sine, and Cosine Integrals).
* H. Davenport, *Multiplicative Number Theory*, Chapter 1.
-/

public section

namespace TauCeti.Real

open Filter MeasureTheory Set
open scoped Topology Nat

/-! ### The exponential-integral series and its entire part -/

/-- The series `∑_{n ≥ 1} y^n / (n * n!)` converges absolutely for every real `y`. -/
theorem summable_pow_div_mul_factorial (y : ℝ) :
    Summable fun n : ℕ ↦ y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
  have hdom : Summable fun n : ℕ ↦ |y| ^ (n + 1) / ((n + 1)! : ℝ) :=
    (summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial |y|)
  refine .of_norm_bounded hdom fun n ↦ ?_
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < ((n : ℝ) + 1)),
    abs_of_pos (by positivity : (0 : ℝ) < ((n + 1)! : ℝ))]
  refine div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg y) _) (by positivity) ?_
  exact le_mul_of_one_le_left (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) n])

/-- The auxiliary continuous series `g(u) = ∑' n, u^n / (n + 1)!` extending `(exp u - 1) / u`
across `u = 0`. -/
private noncomputable def expSubOneDiv (u : ℝ) : ℝ :=
  ∑' n : ℕ, u ^ n / ((n + 1)! : ℝ)

private theorem hasSum_expSubOneDiv_term (u : ℝ) :
    HasSum (fun n : ℕ ↦ u ^ n / ((n + 1)! : ℝ)) (expSubOneDiv u) := by
  refine Summable.hasSum ?_
  refine .of_norm_bounded (Real.summable_pow_div_factorial |u|) fun n ↦ ?_
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < ((n + 1)! : ℝ))]
  refine div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg u) _) (by positivity) ?_
  exact_mod_cast Nat.factorial_le (Nat.le_succ n)

private theorem expSubOneDiv_eq_of_ne_zero {u : ℝ} (hu : u ≠ 0) :
    expSubOneDiv u = (Real.exp u - 1) / u := by
  have hexp : HasSum (fun n : ℕ ↦ u ^ n / (n ! : ℝ)) (Real.exp u) := by
    simpa [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div] using
      (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) u)
  have hshift : HasSum (fun n : ℕ ↦ u ^ (n + 1) / ((n + 1)! : ℝ)) (Real.exp u - 1) := by
    simpa [Finset.sum_range_one] using (hasSum_nat_add_iff' 1).mpr hexp
  have hmul : HasSum (fun n : ℕ ↦ u * (u ^ n / ((n + 1)! : ℝ))) (u * expSubOneDiv u) :=
    (hasSum_expSubOneDiv_term u).mul_left u
  have heq : u * expSubOneDiv u = Real.exp u - 1 := by
    refine hmul.unique ?_
    convert hshift using 1
    ext n
    rw [pow_succ']
    ring
  exact eq_div_of_mul_eq hu (mul_comm (expSubOneDiv u) u ▸ heq)

private theorem continuous_expSubOneDiv : Continuous expSubOneDiv := by
  rw [continuous_iff_continuousAt]
  intro u₀
  have hball : ContinuousOn expSubOneDiv (Metric.closedBall (0 : ℝ) (|u₀| + 1)) := by
    refine continuousOn_tsum (u := fun n ↦ (|u₀| + 1) ^ n / (n ! : ℝ))
      (fun n ↦ by fun_prop) (Real.summable_pow_div_factorial (|u₀| + 1)) fun n u hu ↦ ?_
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hu
    rw [Real.norm_eq_abs, abs_div, abs_pow,
      abs_of_pos (by positivity : (0 : ℝ) < ((n + 1)! : ℝ))]
    refine div_le_div₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg u) hu n) (by positivity) ?_
    exact_mod_cast Nat.factorial_le (Nat.le_succ n)
  exact hball.continuousAt (Metric.closedBall_mem_nhds_of_mem (by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]; linarith))

private theorem integral_expSubOneDiv_eq_tsum (y : ℝ) :
    (∫ u in (0 : ℝ)..y, expSubOneDiv u) =
      ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
  have hsum : HasSum (fun n : ℕ ↦ ∫ u in (0 : ℝ)..y, u ^ n / ((n + 1)! : ℝ))
      (∫ u in (0 : ℝ)..y, expSubOneDiv u) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ ↦ |y| ^ n / (n ! : ℝ))
      (fun n ↦ (by fun_prop : Continuous fun u : ℝ ↦ u ^ n / ((n + 1)! : ℝ)).aestronglyMeasurable)
      (fun n ↦ Eventually.of_forall fun u hu ↦ ?_)
      (Eventually.of_forall fun _ _ ↦ Real.summable_pow_div_factorial |y|)
      intervalIntegrable_const
      (Eventually.of_forall fun u _ ↦ hasSum_expSubOneDiv_term u)
    have habs : |u| ≤ |y| := by
      have hmem := uIoc_subset_uIcc hu
      rcases le_total 0 y with hy | hy
      · rw [uIcc_of_le hy] at hmem
        rw [abs_of_nonneg hmem.1, abs_of_nonneg hy]
        exact hmem.2
      · rw [uIcc_of_ge hy] at hmem
        rw [abs_of_nonpos hmem.2, abs_of_nonpos hy]
        linarith [hmem.1]
    rw [Real.norm_eq_abs, abs_div, abs_pow,
      abs_of_pos (by positivity : (0 : ℝ) < ((n + 1)! : ℝ))]
    refine div_le_div₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg u) habs n) (by positivity) ?_
    exact_mod_cast Nat.factorial_le (Nat.le_succ n)
  rw [← hsum.tsum_eq]
  refine tsum_congr fun n ↦ ?_
  rw [intervalIntegral.integral_div, integral_pow, zero_pow (Nat.succ_ne_zero n), sub_zero,
    div_div, mul_comm]

/-- The entire part `∑_{n ≥ 1} y^n / (n * n!)` of the exponential integral equals
`∫ u in 0..y, (exp u - 1) / u`. -/
theorem integral_exp_sub_one_div_eq_tsum (y : ℝ) :
    (∫ u in (0 : ℝ)..y, (Real.exp u - 1) / u) =
      ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
  rw [← integral_expSubOneDiv_eq_tsum]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [volume.ae_ne (0 : ℝ)] with u hu _
  exact (expSubOneDiv_eq_of_ne_zero hu).symm

/-- The entire-part series `y ↦ ∑_{n ≥ 1} y^n / (n * n!)` is continuous on `ℝ`. -/
theorem continuous_tsum_pow_div_mul_factorial :
    Continuous fun y : ℝ ↦ ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
  have heq : (fun y : ℝ ↦ ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) =
      fun y ↦ ∫ u in (0 : ℝ)..y, expSubOneDiv u :=
    funext fun y ↦ (integral_expSubOneDiv_eq_tsum y).symm
  rw [heq]
  exact intervalIntegral.continuous_primitive
    (fun a b ↦ continuous_expSubOneDiv.intervalIntegrable a b) 0

/-- Derivative of the entire-part series `y ↦ ∑_{n ≥ 1} y^n / (n * n!)` away from `0`. -/
theorem hasDerivAt_tsum_pow_div_mul_factorial {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun t : ℝ ↦ ∑' n : ℕ, t ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)))
      ((Real.exp y - 1) / y) y := by
  have heq : (fun t : ℝ ↦ ∑' n : ℕ, t ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) =
      fun t ↦ ∫ u in (0 : ℝ)..t, expSubOneDiv u :=
    funext fun t ↦ (integral_expSubOneDiv_eq_tsum t).symm
  rw [heq, ← expSubOneDiv_eq_of_ne_zero hy]
  exact intervalIntegral.integral_hasDerivAt_right
    (continuous_expSubOneDiv.intervalIntegrable 0 y)
    continuous_expSubOneDiv.stronglyMeasurable.stronglyMeasurableAtFilter
    continuous_expSubOneDiv.continuousAt

/-! ### Definition and derivative of `li` -/

/-- The **unoffset logarithmic integral**
`li x = γ + log |log x| + ∑_{n ≥ 1} (log x)^n / (n * n!)`.

Mathlib's `Real.log` satisfies `log (-u) = log u`, so `Real.log (Real.log x)` equals
`Real.log |Real.log x|`.
This series defines `li` on `(0, 1) ∪ (1, ∞)` (the value at `x = 1` is junk). For `0 < x < 1` it
equals `∫ t in 0..x, (log t)⁻¹`, and for `x > 1` it equals the Cauchy principal value
`lim_{ε → 0⁺} (∫ t in 0..(1 - ε), (log t)⁻¹ + ∫ t in (1 + ε)..x, (log t)⁻¹)` and satisfies
`Li x = li x - li 2`. -/
noncomputable def li (x : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (Real.log x) +
    ∑' n : ℕ, Real.log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))

/-- Defining equation of `TauCeti.Real.li`. -/
theorem li_def (x : ℝ) :
    li x = Real.eulerMascheroniConstant + Real.log (Real.log x) +
      ∑' n : ℕ, Real.log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := (rfl)

/-- Explicit absolute-value form of `TauCeti.Real.li`. -/
theorem li_eq_add_log_abs (x : ℝ) :
    li x = Real.eulerMascheroniConstant + Real.log |Real.log x| +
      ∑' n : ℕ, Real.log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
  rw [li_def, Real.log_abs]

/-- The unoffset logarithmic integral has derivative `(log x)⁻¹` for every `x > 0`, `x ≠ 1`. -/
theorem hasDerivAt_li {x : ℝ} (hx0 : 0 < x) (hx1 : x ≠ 1) :
    HasDerivAt li (Real.log x)⁻¹ x := by
  have hlog : Real.log x ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hx0 hx1
  have h1 : HasDerivAt (fun t ↦ Real.eulerMascheroniConstant + Real.log (Real.log t))
      ((Real.log x)⁻¹ * x⁻¹) x :=
    ((Real.hasDerivAt_log hlog).comp x (Real.hasDerivAt_log hx0.ne')).const_add
      Real.eulerMascheroniConstant
  have h2 : HasDerivAt
      (fun t ↦ ∑' n : ℕ, Real.log t ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)))
      (((Real.exp (Real.log x) - 1) / Real.log x) * x⁻¹) x :=
    (hasDerivAt_tsum_pow_div_mul_factorial hlog).comp x (Real.hasDerivAt_log hx0.ne')
  refine (h1.add h2).congr_deriv ?_
  rw [Real.exp_log hx0]
  have hxne : x ≠ 0 := hx0.ne'
  field_simp
  ring

/-- `li` is differentiable on `(0, 1)`. -/
theorem differentiableOn_li_Ioo : DifferentiableOn ℝ li (Ioo 0 1) :=
  fun _ hx ↦ (hasDerivAt_li hx.1 hx.2.ne).differentiableAt.differentiableWithinAt

/-- `li` is differentiable on `(1, ∞)`. -/
theorem differentiableOn_li_Ioi : DifferentiableOn ℝ li (Ioi 1) :=
  fun _ hx ↦
    (hasDerivAt_li (zero_lt_one.trans hx) (ne_of_gt hx)).differentiableAt.differentiableWithinAt

/-- `li` is continuous on `(0, 1)`. -/
theorem continuousOn_li_Ioo : ContinuousOn li (Ioo 0 1) :=
  differentiableOn_li_Ioo.continuousOn

/-- `li` is continuous on `(1, ∞)`. -/
theorem continuousOn_li_Ioi : ContinuousOn li (Ioi 1) :=
  differentiableOn_li_Ioi.continuousOn

/-! ### Euler–Mascheroni integral identity and behaviour at `0⁺` -/

/-- `t ↦ log t * exp (-t)` is integrable on `(0, ∞)`. -/
theorem integrableOn_log_mul_exp_neg_Ioi :
    IntegrableOn (fun t : ℝ ↦ Real.log t * Real.exp (-t)) (Ioi 0) := by
  have h := Real.integrableOn_log_log_mul_rpow one_lt_two
  rw [← Real.exp_zero, ← integrableOn_comp_exp_Ioi] at h
  refine h.congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
  simp only [Real.log_exp, smul_eq_mul, ← Real.exp_mul]
  rw [mul_left_comm, ← Real.exp_add]
  ring_nf

/-- `t ↦ exp (-t) / t` is integrable on `(1, ∞)`. -/
theorem integrableOn_exp_neg_div_Ioi :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-t) / t) (Ioi 1) := by
  refine Integrable.mono' (g := fun t : ℝ ↦ Real.exp (-t))
    (integrableOn_exp_neg_Ioi 1)
    ((Real.continuous_exp.comp continuous_neg).measurable.div measurable_id).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 1 < t)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.exp_pos _), abs_of_pos (zero_lt_one.trans ht)]
  exact div_le_self (Real.exp_pos _).le ht.le

/-- `log t * exp (-t) → 0` as `t → ∞`. -/
theorem tendsto_log_mul_exp_neg_atTop :
    Tendsto (fun t : ℝ ↦ Real.log t * Real.exp (-t)) atTop (𝓝 0) := by
  have hle : Tendsto (fun t : ℝ ↦ Real.exp (-t) * t) atTop (𝓝 0) := by
    simpa [Real.rpow_neg_one, div_inv_eq_mul] using
      (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one (-1 : ℝ)).tendsto_div_nhds_zero
  refine squeeze_zero_norm' (a := fun t ↦ Real.exp (-t) * t) ?_ hle
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.log_nonneg ht),
    abs_of_pos (Real.exp_pos _), mul_comm (Real.exp (-t)) t]
  exact mul_le_mul_of_nonneg_right (Real.log_le_self (zero_le_one.trans ht)) (Real.exp_pos _).le

private theorem tendsto_one_sub_exp_neg_mul_log_nhdsGT_zero :
    Tendsto (fun ε : ℝ ↦ (1 - Real.exp (-ε)) * Real.log ε) (𝓝[>] 0) (𝓝 0) := by
  have hc : Tendsto (fun ε : ℝ ↦ expSubOneDiv (-ε)) (𝓝[>] 0) (𝓝 (expSubOneDiv 0)) := by
    simpa [Function.comp_def] using
      ((continuous_expSubOneDiv.comp continuous_neg).tendsto 0).mono_left nhdsWithin_le_nhds
  have hml : Tendsto (fun ε : ℝ ↦ ε * Real.log ε) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Real.continuous_mul_log.tendsto 0).mono_left nhdsWithin_le_nhds
  have h0 : Tendsto (fun ε : ℝ ↦ expSubOneDiv (-ε) * (ε * Real.log ε)) (𝓝[>] 0) (𝓝 0) := by
    simpa using hc.mul hml
  refine h0.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [expSubOneDiv_eq_of_ne_zero (neg_ne_zero.mpr hε.ne')]
  field_simp [hε.ne']
  ring

/-- Integration by parts for `∫ t in 0..z, (1 - exp (-t)) / t` at `z > 0`. -/
private theorem one_sub_exp_neg_mul_log_eq {z : ℝ} (hz : 0 < z) :
    (1 - Real.exp (-z)) * Real.log z =
      (∫ t in Ioc 0 z, Real.log t * Real.exp (-t)) +
        ∫ t in (0 : ℝ)..z, (1 - Real.exp (-t)) / t := by
  have h1 : Tendsto (fun ε : ℝ ↦ (1 - Real.exp (-z)) * Real.log z -
      (1 - Real.exp (-ε)) * Real.log ε) (𝓝[>] 0) (𝓝 ((1 - Real.exp (-z)) * Real.log z)) := by
    simpa using tendsto_const_nhds.sub tendsto_one_sub_exp_neg_mul_log_nhdsGT_zero
  have ha : Tendsto (fun ε : ℝ ↦ ∫ t in ε..z, Real.log t * Real.exp (-t)) (𝓝[>] 0)
      (𝓝 (∫ t in Ioc 0 z, Real.log t * Real.exp (-t))) := by
    have hi_uIcc : IntegrableOn (fun t : ℝ ↦ Real.log t * Real.exp (-t)) (uIcc 0 z) := by
      rw [uIcc_of_le hz.le, integrableOn_Icc_iff_integrableOn_Ioc]
      exact integrableOn_log_mul_exp_neg_Ioi.mono_set Ioc_subset_Ioi_self
    have hcont := intervalIntegral.continuousOn_primitive_interval_left hi_uIcc
    rw [uIcc_of_le hz.le] at hcont
    rw [← intervalIntegral.integral_of_le hz.le]
    have hlim := (hcont 0 ⟨le_rfl, hz.le⟩).tendsto.mono_left
      (nhdsWithin_mono 0 fun t ht ↦ ⟨le_of_lt ht.1, le_of_lt ht.2⟩ : 𝓝[Ioo 0 z] 0 ≤ 𝓝[Icc 0 z] 0)
    rwa [nhdsWithin_Ioo_eq_nhdsGT hz] at hlim
  have hb : Tendsto (fun ε : ℝ ↦ ∫ t in ε..z, (1 - Real.exp (-t)) / t) (𝓝[>] 0)
      (𝓝 (∫ t in (0 : ℝ)..z, (1 - Real.exp (-t)) / t)) := by
    have hcongr (a : ℝ) : (∫ t in a..z, (1 - Real.exp (-t)) / t) =
        ∫ t in a..z, expSubOneDiv (-t) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [volume.ae_ne (0 : ℝ)] with t ht _
      rw [expSubOneDiv_eq_of_ne_zero (neg_ne_zero.mpr ht)]
      field_simp [ht]
      ring
    simp_rw [hcongr]
    have hcont := intervalIntegral.continuousOn_primitive_interval_left
      ((continuous_expSubOneDiv.comp continuous_neg).integrableOn_uIcc (μ := volume) (a := 0)
        (b := z))
    rw [uIcc_of_le hz.le] at hcont
    have hlim := (hcont 0 ⟨le_rfl, hz.le⟩).tendsto.mono_left
      (nhdsWithin_mono 0 fun t ht ↦ ⟨le_of_lt ht.1, le_of_lt ht.2⟩ : 𝓝[Ioo 0 z] 0 ≤ 𝓝[Icc 0 z] 0)
    rwa [nhdsWithin_Ioo_eq_nhdsGT hz] at hlim
  refine tendsto_nhds_unique h1 ((ha.add hb).congr' ?_)
  filter_upwards [Ioo_mem_nhdsGT hz] with ε ⟨hε0, hεz⟩
  have hlog_int : IntervalIntegrable (fun t : ℝ ↦ Real.log t * Real.exp (-t)) volume ε z := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
    rw [uIcc_of_le hεz.le] at ht
    have ht0 : 0 < t := hε0.trans_le ht.1
    fun_prop (disch := positivity)
  have hsub_int : IntervalIntegrable (fun t : ℝ ↦ (1 - Real.exp (-t)) / t) volume ε z := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
    rw [uIcc_of_le hεz.le] at ht
    have ht0 : 0 < t := hε0.trans_le ht.1
    fun_prop (disch := positivity)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := ε) (b := z)
    (f := fun t : ℝ ↦ (1 - Real.exp (-t)) * Real.log t)
    (f' := fun t : ℝ ↦ Real.log t * Real.exp (-t) + (1 - Real.exp (-t)) / t)
    (fun t ht ↦ by
      rw [uIcc_of_le hεz.le] at ht
      have ht0 : 0 < t := hε0.trans_le ht.1
      have hd1 : HasDerivAt (fun u : ℝ ↦ 1 - Real.exp (-u)) (Real.exp (-t)) t := by
        simpa using (hasDerivAt_neg t).exp.const_sub 1
      exact (hd1.mul (Real.hasDerivAt_log ht0.ne')).congr_deriv (by ring))
    (hlog_int.add hsub_int)
  rwa [intervalIntegral.integral_add hlog_int hsub_int] at hFTC

/-- **Integral representation of the Euler–Mascheroni constant**:
`γ = ∫ t in 0..1, (1 - exp (-t)) / t - ∫ t in Ioi 1, exp (-t) / t`. -/
theorem eulerMascheroniConstant_eq_integral_sub_integral :
    Real.eulerMascheroniConstant =
      (∫ t in (0 : ℝ)..1, (1 - Real.exp (-t)) / t) -
        ∫ t in Ioi (1 : ℝ), Real.exp (-t) / t := by
  have h1 : (∫ t in (0 : ℝ)..1, (1 - Real.exp (-t)) / t) =
      -(∫ t in Ioc 0 1, Real.log t * Real.exp (-t)) := by
    have h := one_sub_exp_neg_mul_log_eq one_pos
    rw [Real.log_one, mul_zero] at h
    linarith
  have h2 : (∫ t in Ioi (1 : ℝ), Real.exp (-t) / t) =
      ∫ t in Ioi (1 : ℝ), Real.log t * Real.exp (-t) := by
    have hint_log : IntegrableOn (fun t : ℝ ↦ Real.log t * Real.exp (-t)) (Ioi 1) :=
      integrableOn_log_mul_exp_neg_Ioi.mono_set (Ioi_subset_Ioi zero_le_one)
    have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto'
      (a := (1 : ℝ)) (f := fun t : ℝ ↦ -(Real.exp (-t) * Real.log t))
      (f' := fun t : ℝ ↦ Real.log t * Real.exp (-t) - Real.exp (-t) / t) (m := 0)
      (fun t ht ↦ by
        have ht0 : 0 < t := zero_lt_one.trans_le ht
        have hd1 : HasDerivAt (fun u : ℝ ↦ Real.exp (-u)) (-Real.exp (-t)) t := by
          simpa using (hasDerivAt_neg t).exp
        exact ((hd1.mul (Real.hasDerivAt_log ht0.ne')).neg).congr_deriv (by ring))
      (hint_log.sub integrableOn_exp_neg_div_Ioi)
      (by simpa [mul_comm] using tendsto_log_mul_exp_neg_atTop.neg)
    rw [Real.log_one, mul_zero, neg_zero, sub_zero,
      integral_sub hint_log integrableOn_exp_neg_div_Ioi] at hFTC
    linarith
  have hsplit : (∫ t in Ioi (0 : ℝ), Real.log t * Real.exp (-t)) =
      (∫ t in Ioc (0 : ℝ) 1, Real.log t * Real.exp (-t)) +
        ∫ t in Ioi (1 : ℝ), Real.log t * Real.exp (-t) := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (integrableOn_log_mul_exp_neg_Ioi.mono_set Ioc_subset_Ioi_self)
      (integrableOn_log_mul_exp_neg_Ioi.mono_set (Ioi_subset_Ioi zero_le_one)),
      Ioc_union_Ioi_eq_Ioi zero_le_one]
  rw [h1, h2, Real.eulerMascheroniConstant_eq_neg_integral_log, hsplit]
  ring

/-- `li x → 0` as `x → 0⁺`. -/
theorem tendsto_li_nhdsGT_zero : Tendsto li (𝓝[>] 0) (𝓝 0) := by
  have hformula (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
      li x = Real.eulerMascheroniConstant +
        Real.log (-Real.log x) * Real.exp (-(-Real.log x)) +
        ∫ t in Ioc 0 (-Real.log x), Real.log t * Real.exp (-t) := by
    set z : ℝ := -Real.log x
    have hz : 0 < z := neg_pos.mpr (Real.log_neg hx0 hx1)
    have hseries : (∑' n : ℕ, Real.log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) =
        -(∫ t in (0 : ℝ)..z, (1 - Real.exp (-t)) / t) := by
      rw [← integral_exp_sub_one_div_eq_tsum (Real.log x)]
      have hsub := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := z)
        (f := fun u : ℝ ↦ (Real.exp u - 1) / u)
      have hneg_z : -z = Real.log x := neg_neg (Real.log x)
      rw [neg_zero, hneg_z, intervalIntegral.integral_symm (0 : ℝ) (Real.log x)] at hsub
      have hneg : (∫ u in (0 : ℝ)..Real.log x, (Real.exp u - 1) / u) =
          -(∫ t in (0 : ℝ)..z, (Real.exp (-t) - 1) / -t) := by linarith
      rw [hneg]
      congr 1
      refine intervalIntegral.integral_congr fun t _ ↦ by ring
    have hibp := one_sub_exp_neg_mul_log_eq hz
    have hlogz : Real.log (Real.log x) = Real.log z := (Real.log_neg_eq_log (Real.log x)).symm
    rw [li_def, hseries, hlogz]
    linarith
  have hz_top : Tendsto (fun x : ℝ ↦ -Real.log x) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hterm2 : Tendsto (fun z : ℝ ↦ ∫ t in Ioc 0 z, Real.log t * Real.exp (-t)) atTop
      (𝓝 (∫ t in Ioi 0, Real.log t * Real.exp (-t))) := by
    refine (intervalIntegral_tendsto_integral_Ioi (a := (0 : ℝ))
      integrableOn_log_mul_exp_neg_Ioi tendsto_id).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with z hz
    exact intervalIntegral.integral_of_le hz
  have hlim : Tendsto
      (fun x : ℝ ↦ Real.eulerMascheroniConstant +
        Real.log (-Real.log x) * Real.exp (-(-Real.log x)) +
        ∫ t in Ioc 0 (-Real.log x), Real.log t * Real.exp (-t))
      (𝓝[>] 0) (𝓝 0) := by
    have hsum := ((tendsto_const_nhds (x := Real.eulerMascheroniConstant)).add
      (tendsto_log_mul_exp_neg_atTop.comp hz_top)).add (hterm2.comp hz_top)
    have hzero : Real.eulerMascheroniConstant + 0 +
        ∫ t in Ioi (0 : ℝ), Real.log t * Real.exp (-t) = 0 := by
      rw [Real.eulerMascheroniConstant_eq_neg_integral_log]
      ring
    rwa [hzero] at hsum
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with x ⟨hx0, hx1⟩
  exact (hformula x hx0 hx1).symm

/-! ### Relation with `Li`, monotonicity, sign, and Soldner's constant -/

/-- **Offset identity**: for every `x > 1`, `Li x = li x - li 2`. -/
theorem logIntegral_eq_li_sub_li_two {x : ℝ} (hx : 1 < x) :
    logIntegral x = li x - li 2 := by
  rw [logIntegral_def]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht ↦ ?_)
    (by simpa [pow_one] using intervalIntegrable_inv_log_pow 1 one_lt_two hx)
  have ht1 : 1 < t := by
    rcases mem_uIcc.mp ht with h | h
    · exact one_lt_two.trans_le h.1
    · exact hx.trans_le h.1
  exact hasDerivAt_li (zero_lt_one.trans ht1) ht1.ne'

/-- Rearranged offset identity: for every `x > 1`, `li x = Li x + li 2`. -/
theorem li_eq_logIntegral_add_li_two {x : ℝ} (hx : 1 < x) :
    li x = logIntegral x + li 2 := by
  linarith [logIntegral_eq_li_sub_li_two hx]

/-- `li` is strictly decreasing on `(0, 1)`. -/
theorem strictAntiOn_li_Ioo : StrictAntiOn li (Ioo 0 1) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioo 0 1) continuousOn_li_Ioo fun x hx ↦ ?_
  rw [interior_Ioo] at hx
  rw [(hasDerivAt_li hx.1 hx.2.ne).deriv]
  exact inv_lt_zero.mpr (Real.log_neg hx.1 hx.2)

/-- `li` is strictly negative on `(0, 1)`. -/
theorem li_neg {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : li x < 0 := by
  have hle : li (x / 2) ≤ 0 := by
    refine le_of_tendsto_of_tendsto tendsto_const_nhds tendsto_li_nhdsGT_zero ?_
    filter_upwards [Ioo_mem_nhdsGT (half_pos hx0)] with y ⟨hy0, hyx⟩
    exact (strictAntiOn_li_Ioo ⟨hy0, hyx.trans (by linarith)⟩
      ⟨half_pos hx0, by linarith⟩ hyx).le
  exact (strictAntiOn_li_Ioo ⟨half_pos hx0, by linarith⟩ ⟨hx0, hx1⟩ (by linarith)).trans_le hle

/-- `li` is strictly increasing on `(1, ∞)`. -/
theorem strictMonoOn_li_Ioi : StrictMonoOn li (Ioi 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 1) continuousOn_li_Ioi fun x hx ↦ ?_
  rw [interior_Ioi] at hx
  rw [(hasDerivAt_li (zero_lt_one.trans hx) hx.ne').deriv]
  exact inv_pos.mpr (Real.log_pos hx)

/-- `li x → -∞` as `x → 1⁺`. -/
theorem tendsto_li_nhdsGT_one : Tendsto li (𝓝[>] 1) atBot := by
  have hlog : Tendsto (fun x : ℝ ↦ Real.log (Real.log x)) (𝓝[>] 1) atBot := by
    refine Real.tendsto_log_nhdsGT_zero.comp ?_
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by simpa [Real.log_one] using
        (Real.continuousAt_log one_ne_zero).tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
    exact Real.log_pos hx
  have hser : Tendsto
      (fun x : ℝ ↦ ∑' n : ℕ, Real.log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)))
      (𝓝[>] 1) (𝓝 0) := by
    have hc : ContinuousAt
        (fun x : ℝ ↦ ∑' n : ℕ, Real.log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) 1 :=
      continuous_tsum_pow_div_mul_factorial.continuousAt.comp (Real.continuousAt_log one_ne_zero)
    simpa [Real.log_one] using hc.tendsto.mono_left nhdsWithin_le_nhds
  refine ((tendsto_atBot_add_const_left _ Real.eulerMascheroniConstant hlog).atBot_add
    hser).congr fun x ↦ ?_
  rw [li_def]

/-- `li x → -∞` as `x → 1⁻`. -/
theorem tendsto_li_nhdsLT_one : Tendsto li (𝓝[<] 1) atBot := by
  have hlog : Tendsto (fun x : ℝ ↦ Real.log (Real.log x)) (𝓝[<] 1) atBot := by
    refine Real.tendsto_log_nhdsNE_zero.comp ?_
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by simpa [Real.log_one] using
        (Real.continuousAt_log one_ne_zero).tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [Ioo_mem_nhdsLT one_pos] with x ⟨hx0, hx1⟩
    exact (Real.log_neg hx0 hx1).ne
  have hser : Tendsto
      (fun x : ℝ ↦ ∑' n : ℕ, Real.log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)))
      (𝓝[<] 1) (𝓝 0) := by
    have hc : ContinuousAt
        (fun x : ℝ ↦ ∑' n : ℕ, Real.log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ))) 1 :=
      continuous_tsum_pow_div_mul_factorial.continuousAt.comp (Real.continuousAt_log one_ne_zero)
    simpa [Real.log_one] using hc.tendsto.mono_left nhdsWithin_le_nhds
  refine ((tendsto_atBot_add_const_left _ Real.eulerMascheroniConstant hlog).atBot_add
    hser).congr fun x ↦ ?_
  rw [li_def]

/-- `li x → +∞` as `x → +∞`. -/
theorem tendsto_li_atTop : Tendsto li atTop atTop := by
  have hLi : Tendsto logIntegral atTop atTop :=
    logIntegral_isEquivalent_div_log.tendsto_atTop_iff.mpr tendsto_div_log_atTop
  refine (tendsto_atTop_add_const_right _ (li 2) hLi).congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact (li_eq_logIntegral_add_li_two hx).symm

/-- `li x > 0` for every `x ≥ 3 / 2`. -/
theorem li_pos_of_three_halves_le {x : ℝ} (hx : (3 : ℝ) / 2 ≤ x) : 0 < li x := by
  suffices h32 : 0 < li (3 / 2) by
    rcases eq_or_lt_of_le hx with rfl | hlt
    · exact h32
    · exact h32.trans (strictMonoOn_li_Ioi (by norm_num) (mem_Ioi.mpr (by linarith)) hlt)
  -- Show `0.4054 < log (3 / 2)` via `exp 0.4054 < 3 / 2`.
  have hlog32 : (0.4054 : ℝ) < Real.log (3 / 2) := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have hb := Real.exp_bound' (x := (0.4054 : ℝ)) (by norm_num) (by norm_num) (n := 6) (by decide)
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at hb
    norm_num at hb ⊢
    linarith
  -- Show `-0.903 < log (log (3 / 2))` via `1 < 0.4054 * exp 0.903`.
  have hloglog : (-0.903 : ℝ) < Real.log (Real.log (3 / 2)) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have he := Real.sum_le_exp_of_nonneg (x := (903 / 1000 : ℝ)) (by norm_num) 8
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at he
    norm_num at he
    have hexp_mul : Real.exp (-(903 / 1000 : ℝ)) * Real.exp (903 / 1000) = 1 := by
      rw [← Real.exp_add]; norm_num
    have hlt : Real.exp (-(903 / 1000 : ℝ)) < 4054 / 10000 := by nlinarith
    have hlt' : Real.exp (-0.903) < 0.4054 := by norm_num at hlt ⊢; exact hlt
    exact hlt'.trans hlog32
  -- First two terms of the positive series at `log (3 / 2)`.
  have hser : (0.446 : ℝ) <
      ∑' n : ℕ, Real.log (3 / 2) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
    have hsum := summable_pow_div_mul_factorial (Real.log (3 / 2))
    have hnonneg (n : ℕ) :
        0 ≤ Real.log (3 / 2) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
      have : 0 < Real.log (3 / 2) := by linarith
      positivity
    have hge := hsum.sum_le_tsum (Finset.range 2) (fun n _ ↦ hnonneg n)
    have htwo : (0.446 : ℝ) <
        ∑ n ∈ Finset.range 2,
          Real.log (3 / 2) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1)! : ℝ)) := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
        Nat.cast_zero, Nat.cast_one, Nat.factorial]
      norm_num
      nlinarith
    exact htwo.trans_le hge
  rw [li_def]
  linarith [Real.one_half_lt_eulerMascheroniConstant]

/-- `li 2 > 0`. -/
theorem li_two_pos : 0 < li 2 :=
  li_pos_of_three_halves_le (by norm_num)

/-- The unoffset logarithmic integral `li` differs from the offset logarithmic integral `Li`. -/
theorem li_ne_logIntegral : li ≠ logIntegral := by
  intro h
  have h2 := congr_fun h 2
  rw [logIntegral_two] at h2
  linarith [li_two_pos]

/-- **Soldner's constant**: `li` has a unique zero in `(1, ∞)`. -/
theorem existsUnique_li_eq_zero : ∃! μ ∈ Ioi (1 : ℝ), li μ = 0 := by
  obtain ⟨a, ha1, ha_lt⟩ : ∃ a ∈ Ioo (1 : ℝ) (3 / 2), li a < 0 := by
    have hmem : ∀ᶠ t in 𝓝[>] (1 : ℝ), li t < 0 :=
      tendsto_li_nhdsGT_one.eventually (eventually_lt_atBot 0)
    exact (hmem.and (Ioo_mem_nhdsGT (by norm_num : (1 : ℝ) < 3 / 2))).exists.imp fun a ⟨h1, h2⟩ ↦
      ⟨h2, h1⟩
  have hcont : ContinuousOn li (Icc a (3 / 2)) :=
    continuousOn_li_Ioi.mono fun t ht ↦ ha1.1.trans_le ht.1
  have h0 : (0 : ℝ) ∈ Icc (li a) (li (3 / 2)) := ⟨ha_lt.le, (li_pos_of_three_halves_le le_rfl).le⟩
  obtain ⟨μ, hμ, hliμ⟩ := intermediate_value_Icc ha1.2.le hcont h0
  refine ⟨μ, ⟨ha1.1.trans_le hμ.1, hliμ⟩, fun y ⟨hy1, hliy⟩ ↦ ?_⟩
  exact strictMonoOn_li_Ioi.injOn hy1 (ha1.1.trans_le hμ.1) (hliy.trans hliμ.symm)

end TauCeti.Real
