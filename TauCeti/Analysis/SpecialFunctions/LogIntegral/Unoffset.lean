/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import TauCeti.Analysis.SpecialFunctions.LogIntegral.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import TauCeti.Analysis.SpecialFunctions.Exp.DividedDifference

/-!
# The unoffset logarithmic integral

This file defines the unoffset logarithmic integral `TauCeti.Real.li` through its globally
convergent exponential-integral series
`li x = γ + log |log x| + ∑' n : ℕ, (log x) ^ (n + 1) / ((n + 1) * (n + 1)!)`,
where `γ = Real.eulerMascheroniConstant` and Mathlib's `Real.log` satisfies
`Real.log (-u) = Real.log u`, so the series matches the classical exponential integral
`Ei (log x)` for every `x > 0` with `x ≠ 1` (the value at `x = 1` is the junk value `γ`).

Using the power series as the definition avoids the nonintegrable singularity of `(log t)⁻¹` at
`t = 1` and yields its derivative `(log x)⁻¹`, the offset relation `Li x = li x - li 2`, the
exponential-integral representations on both half-lines, the limit `li x → 0` as `x → 0⁺`,
monotonicity, sign, and the existence and uniqueness of Soldner's constant. Cauchy principal value
and absolutely convergent integral representations in the variable `t` are established in
`TauCeti.Analysis.SpecialFunctions.LogIntegral.PrincipalValue`.

## Main declarations

* `TauCeti.Real.li` — the unoffset logarithmic integral.
* `TauCeti.Real.hasDerivAt_li` — derivative `(log x)⁻¹` for `x > 0`, `x ≠ 1`.
* `TauCeti.Real.integral_exp_sub_one_div_eq_tsum` — `∫ t in 0..y, (exp t - 1) / t` equals the
  power series `∑' n, y ^ (n + 1) / ((n + 1) * (n + 1)!)`.
* `TauCeti.Real.eulerMascheroniConstant_eq_integral_Ioc_sub_integral_Ioi` —
  `γ = ∫ t in Ioc 0 1, (1 - exp (-t)) / t - ∫ t in Ioi 1, exp (-t) / t`.
* `TauCeti.Real.integral_Iic_exp_div_eq_li` and `TauCeti.Real.tendsto_pv_exp_div_eq_li` — the
  exponential-integral representations of `li (exp y)` for `y < 0` and `y > 0`.
* `TauCeti.Real.tendsto_li_nhdsGT_zero` — `li x → 0` as `x → 0⁺`.
* `TauCeti.Real.logIntegral_eq_li_sub_li_two` — `Li x = li x - li 2` for `x > 1`.
* `TauCeti.Real.strictAntiOn_li`, `TauCeti.Real.strictMonoOn_li`,
  `TauCeti.Real.li_pos_of_three_halves_le`, and `TauCeti.Real.existsUnique_li_eq_zero` —
  monotonicity, sign, positivity from `3 / 2`, and existence and uniqueness of Soldner's constant.

## References

* F. W. J. Olver et al., *NIST Digital Library of Mathematical Functions*, §6.2.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.
-/

public section

namespace TauCeti.Real

open Filter MeasureTheory Set
open scoped Topology

/-! ### The exponential-integral power series -/

/-- The divided difference `dslope Real.exp 0` (`u ↦ (exp u - 1) / u`, extended by `1` at `0`)
is continuous on `ℝ`. -/
theorem continuous_dslope_exp_zero : Continuous (dslope Real.exp 0) :=
  (Real.contDiff_dslope_exp 0).continuous.comp (continuous_const.prodMk continuous_id)

/-- The power series `∑' n : ℕ, y ^ (n + 1) / ((n + 1) * (n + 1)!)` converges absolutely for every
real `y`, its terms being bounded in norm by `|y| ^ (n + 1) / (n + 1)!`. -/
theorem summable_pow_div_mul_factorial (y : ℝ) :
    Summable fun n : ℕ ↦ y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ)) := by
  have hexp : Summable fun n : ℕ ↦ |y| ^ (n + 1) / ((n + 1).factorial : ℝ) :=
    (Real.summable_pow_div_factorial |y|).comp_injective Nat.succ_injective
  refine hexp.of_norm_bounded fun n ↦ ?_
  have hfac : (0 : ℝ) < ((n + 1).factorial : ℝ) := by positivity
  have hden : (0 : ℝ) < ((n : ℝ) + 1) * ((n + 1).factorial : ℝ) := by positivity
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hden]
  exact div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg y) _) hfac
    (le_mul_of_one_le_left hfac.le h1)

/-- The series `∑' n : ℕ, y ^ n / (n + 1)!` sums to `dslope Real.exp 0 y`, i.e., `1` at `y = 0`
and `(exp y - 1) / y` for `y ≠ 0`. -/
theorem tsum_pow_div_succ_factorial (y : ℝ) :
    (∑' n : ℕ, y ^ n / ((n + 1).factorial : ℝ)) = dslope Real.exp 0 y := by
  by_cases hy : y = 0
  · subst hy
    rw [dslope_same, (Real.hasDerivAt_exp 0).deriv, Real.exp_zero, tsum_eq_single 0]
    · simp
    · intro n hn
      simp [zero_pow hn]
  · rw [dslope_of_ne _ hy, slope_def_field, sub_zero, Real.exp_zero]
    have hmul : y * (∑' n : ℕ, y ^ n / ((n + 1).factorial : ℝ)) = Real.exp y - 1 := by
      rw [← tsum_mul_left]
      have hshift : (∑' n : ℕ, y * (y ^ n / ((n + 1).factorial : ℝ))) =
          ∑' n : ℕ, y ^ (n + 1) / ((n + 1).factorial : ℝ) := by
        congr 1; ext n; rw [pow_succ', mul_div_assoc]
      rw [hshift]
      have hexp : Real.exp y = ∑' n : ℕ, y ^ n / (n.factorial : ℝ) := by
        rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      have hsplit := (Real.summable_pow_div_factorial y).tsum_eq_zero_add
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at hsplit
      linarith
    exact eq_div_of_mul_eq hy (by linarith [mul_comm y (∑' n : ℕ, y ^ n / ((n + 1).factorial : ℝ))])

/-- Termwise differentiation of the exponential-integral series: its derivative at every real `y`
is the divided difference `dslope Real.exp 0 y`. -/
theorem hasDerivAt_tsum_pow_div_mul_factorial (y : ℝ) :
    HasDerivAt
      (fun z : ℝ ↦ ∑' n : ℕ, z ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ)))
      (dslope Real.exp 0 y) y := by
  let R : ℝ := |y| + 1
  have hR : 0 < R := by positivity
  have hu : Summable fun n : ℕ ↦ R ^ n / (n.factorial : ℝ) := Real.summable_pow_div_factorial R
  have hderiv := hasDerivAt_tsum_of_isPreconnected (t := Ioo (-R) R) (y := y)
    (g := fun (n : ℕ) (z : ℝ) ↦ z ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ)))
    (g' := fun (n : ℕ) (z : ℝ) ↦ z ^ n / ((n + 1).factorial : ℝ))
    (y₀ := 0) hu isOpen_Ioo isPreconnected_Ioo
    (fun n z _ ↦ by
      have h := (hasDerivAt_pow (n + 1) z).div_const
        (((n : ℝ) + 1) * ((n + 1).factorial : ℝ))
      refine h.congr_deriv ?_
      have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp)
    (fun n z hz ↦ by
      have hfac : (0 : ℝ) < ((n + 1).factorial : ℝ) := by positivity
      rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hfac]
      have hzR : |z| ≤ R := (abs_lt.mpr hz).le
      calc |z| ^ n / ((n + 1).factorial : ℝ)
          ≤ R ^ n / ((n + 1).factorial : ℝ) := by gcongr
        _ ≤ R ^ n / (n.factorial : ℝ) := by
            gcongr
            exact Nat.le_succ n)
    (by simp [hR])
    (by
      convert summable_zero (α := ℝ) (β := ℕ) using 1
      ext n
      simp [zero_pow (Nat.succ_ne_zero n)])
    (by
      rw [mem_Ioo]
      constructor <;> linarith [le_abs_self y, neg_le_abs y])
  rwa [tsum_pow_div_succ_factorial] at hderiv

/-- The integral of `dslope Real.exp 0` from `0` to `y` equals the exponential-integral series. -/
theorem integral_dslope_exp_eq_tsum (y : ℝ) :
    ∫ t in (0 : ℝ)..y, dslope Real.exp 0 t =
      ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ)) := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ ↦ hasDerivAt_tsum_pow_div_mul_factorial t)
    (continuous_dslope_exp_zero.intervalIntegrable 0 y)
  have h0 : (∑' n : ℕ, (0 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ))) = 0 := by
    simp [zero_pow (Nat.succ_ne_zero _)]
  rw [h0, sub_zero] at hFTC
  exact hFTC

/-- The integral `∫ t in 0..y, (exp t - 1) / t` equals the exponential-integral power series
for every real `y`. -/
theorem integral_exp_sub_one_div_eq_tsum (y : ℝ) :
    ∫ t in (0 : ℝ)..y, (Real.exp t - 1) / t =
      ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ)) := by
  rw [← integral_dslope_exp_eq_tsum]
  refine intervalIntegral.integral_congr_ae ?_
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [hne] with t ht _
  rw [dslope_of_ne _ ht, slope_def_field, sub_zero, Real.exp_zero]

/-! ### Euler–Mascheroni integral representation -/

/-- The function `t ↦ exp (-t) / t` is integrable on `(a, ∞)` for every `a > 0`. -/
theorem integrableOn_exp_neg_div_Ioi {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-t) / t) (Ioi a) := by
  have hexp : IntegrableOn (fun t : ℝ ↦ a⁻¹ * Real.exp (-t)) (Ioi a) := by
    simpa [IntegrableOn, neg_one_mul] using
      (integrableOn_exp_mul_Ioi (a := -1) (by norm_num) a).const_mul a⁻¹
  refine hexp.mono' (by fun_prop : Measurable fun t : ℝ ↦ Real.exp (-t) / t).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : a < t)
  rw [Real.norm_eq_abs, abs_of_pos (div_pos (Real.exp_pos _) (ha.trans ht)), div_eq_inv_mul]
  gcongr

/-- The function `t ↦ (1 - exp (-t)) / t` is integrable on `(0, a]` for every `a ≥ 0`. -/
theorem integrableOn_one_sub_exp_neg_div_Ioc {a : ℝ} :
    IntegrableOn (fun t : ℝ ↦ (1 - Real.exp (-t)) / t) (Ioc 0 a) := by
  have hcont : Continuous (fun t : ℝ ↦ dslope Real.exp 0 (-t)) :=
    continuous_dslope_exp_zero.comp continuous_neg
  refine (hcont.integrableOn_Ioc (a := 0) (b := a)).congr_fun (fun t ht ↦ ?_) measurableSet_Ioc
  have ht0 : -t ≠ 0 := neg_ne_zero.mpr ht.1.ne'
  dsimp only
  rw [dslope_of_ne _ ht0, slope_def_field, sub_zero, Real.exp_zero, div_neg, ← neg_div, neg_sub]

/-- The function `t ↦ log t * exp (-t)` is integrable on `(0, ∞)`. -/
theorem integrableOn_log_mul_exp_neg_Ioi :
    IntegrableOn (fun t : ℝ ↦ Real.log t * Real.exp (-t)) (Ioi 0) := by
  have hmaj : IntegrableOn (fun t : ℝ ↦ (2 * t ^ (-(1 / 2 : ℝ)) + t) * Real.exp (-t)) (Ioi 0) := by
    have h1 : IntegrableOn (fun t : ℝ ↦ 2 * (t ^ (-(1 / 2 : ℝ)) * Real.exp (-t))) (Ioi 0) := by
      simpa [IntegrableOn, neg_one_mul, Real.rpow_one] using
        (integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num : (-1 : ℝ) < -(1 / 2)) one_pos
          one_pos).const_mul 2
    have h2 : IntegrableOn (fun t : ℝ ↦ t ^ (1 : ℝ) * Real.exp (-t)) (Ioi 0) := by
      simpa [IntegrableOn, neg_one_mul, Real.rpow_one] using
        integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num : (-1 : ℝ) < 1) one_pos one_pos
    refine (h1.add h2).congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
    simp only [Pi.add_apply, Real.rpow_one]
    ring
  refine hmaj.mono'
    (by fun_prop : Measurable fun t : ℝ ↦ Real.log t * Real.exp (-t)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  gcongr
  rw [abs_le]
  have hlo : -(2 * t ^ (-(1 / 2 : ℝ))) ≤ Real.log t := by
    simpa [div_eq_mul_inv, mul_comm] using
      Real.neg_rpow_div_le_log ht.le (by norm_num : (0 : ℝ) < 1 / 2)
  have hhi := Real.log_le_self ht.le
  constructor <;> linarith [hlo, hhi, Real.rpow_nonneg ht.le (-(1 / 2 : ℝ))]

/-- Integration by parts on `(0, 1]`:
`∫ t in Ioc 0 1, log t * exp (-t) = -∫ t in Ioc 0 1, (1 - exp (-t)) / t`. -/
theorem integral_Ioc_log_mul_exp_neg :
    (∫ t in Ioc (0 : ℝ) 1, Real.log t * Real.exp (-t)) =
      -∫ t in Ioc (0 : ℝ) 1, (1 - Real.exp (-t)) / t := by
  have hint_01 : IntegrableOn (fun t : ℝ ↦ Real.log t * Real.exp (-t)) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one, integrableOn_Icc_iff_integrableOn_Ioc]
    exact integrableOn_log_mul_exp_neg_Ioi.mono_set Ioc_subset_Ioi_self
  have hint_sub : IntegrableOn (fun t : ℝ ↦ (1 - Real.exp (-t)) / t) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one, integrableOn_Icc_iff_integrableOn_Ioc]
    exact integrableOn_one_sub_exp_neg_div_Ioc
  have hLHS : Tendsto (fun ε : ℝ ↦ ∫ t in ε..1, Real.log t * Real.exp (-t))
      (𝓝[>] 0) (𝓝 (∫ t in Ioc (0 : ℝ) 1, Real.log t * Real.exp (-t))) := by
    have hc := (intervalIntegral.continuousOn_primitive_interval_left (μ := volume) hint_01 0
      left_mem_uIcc).mono_of_mem_nhdsWithin
      (by rw [uIcc_of_le zero_le_one]; exact Icc_mem_nhdsGT zero_lt_one)
    simpa [intervalIntegral.integral_of_le zero_le_one] using hc.tendsto
  have hRHS_int : Tendsto (fun ε : ℝ ↦ ∫ t in ε..1, (1 - Real.exp (-t)) / t)
      (𝓝[>] 0) (𝓝 (∫ t in Ioc (0 : ℝ) 1, (1 - Real.exp (-t)) / t)) := by
    have hc := (intervalIntegral.continuousOn_primitive_interval_left (μ := volume) hint_sub 0
      left_mem_uIcc).mono_of_mem_nhdsWithin
      (by rw [uIcc_of_le zero_le_one]; exact Icc_mem_nhdsGT zero_lt_one)
    simpa [intervalIntegral.integral_of_le zero_le_one] using hc.tendsto
  have hbdry : Tendsto (fun ε : ℝ ↦ (1 - Real.exp (-ε)) * Real.log ε) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun ε : ℝ ↦ dslope Real.exp 0 (-ε)) (𝓝[>] 0) (𝓝 1) := by
      have hcont : Continuous (fun ε : ℝ ↦ dslope Real.exp 0 (-ε)) :=
        continuous_dslope_exp_zero.comp continuous_neg
      simpa [dslope_same, (Real.hasDerivAt_exp 0).deriv] using
        (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun ε : ℝ ↦ Real.log ε * ε) (𝓝[>] 0) (𝓝 0) := by
      simpa [Real.rpow_one] using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
    have hmul : Tendsto (fun ε : ℝ ↦ dslope Real.exp 0 (-ε) * (Real.log ε * ε))
        (𝓝[>] 0) (𝓝 0) := by
      simpa using h1.mul h2
    refine hmul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [dslope_of_ne _ (neg_ne_zero.mpr hε.ne'), slope_def_field, sub_zero, Real.exp_zero]
    field_simp [hε.ne']
    ring
  have hEq : (fun ε : ℝ ↦ ∫ t in ε..1, Real.log t * Real.exp (-t)) =ᶠ[𝓝[>] 0]
      fun ε : ℝ ↦ -((1 - Real.exp (-ε)) * Real.log ε) - ∫ t in ε..1, (1 - Real.exp (-t)) / t := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
    have hpos : ∀ t ∈ uIcc ε 1, 0 < t := fun t ht ↦ by
      rw [uIcc_of_le hε.2.le] at ht
      exact hε.1.trans_le ht.1
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := ε) (b := 1)
      (u := fun t ↦ Real.log t) (u' := fun t ↦ t⁻¹)
      (v := fun t ↦ 1 - Real.exp (-t)) (v' := fun t ↦ Real.exp (-t))
      (fun t ht ↦ Real.hasDerivAt_log (hpos t ht).ne')
      (fun t _ ↦ by
        have h := (hasDerivAt_const t (1 : ℝ)).fun_sub
          ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t))
        simpa using h)
      (ContinuousOn.intervalIntegrable fun t ht ↦
        (continuousAt_inv₀ (hpos t ht).ne').continuousWithinAt)
      ((by fun_prop : Continuous fun t : ℝ ↦ Real.exp (-t)).intervalIntegrable ε 1)
    have hcomm : (∫ t in ε..1, t⁻¹ * (1 - Real.exp (-t))) =
        ∫ t in ε..1, (1 - Real.exp (-t)) / t := by
      congr 1; ext t; ring
    rw [hcomm, Real.log_one, zero_mul, zero_sub] at hibp
    linarith [mul_comm (Real.log ε) (1 - Real.exp (-ε))]
  exact tendsto_nhds_unique (hLHS.congr' hEq) (by simpa using hbdry.neg.sub hRHS_int)

/-- Integration by parts on `(1, ∞)`:
`∫ t in Ioi 1, log t * exp (-t) = ∫ t in Ioi 1, exp (-t) / t`. -/
theorem integral_Ioi_log_mul_exp_neg :
    (∫ t in Ioi (1 : ℝ), Real.log t * Real.exp (-t)) =
      ∫ t in Ioi (1 : ℝ), Real.exp (-t) / t := by
  have hint_1inf : IntegrableOn (fun t : ℝ ↦ Real.log t * Real.exp (-t)) (Ioi 1) :=
    integrableOn_log_mul_exp_neg_Ioi.mono_set (Ioi_subset_Ioi zero_le_one)
  have hLHS : Tendsto (fun R : ℝ ↦ ∫ t in (1 : ℝ)..R, Real.log t * Real.exp (-t))
      atTop (𝓝 (∫ t in Ioi (1 : ℝ), Real.log t * Real.exp (-t))) :=
    intervalIntegral_tendsto_integral_Ioi 1 hint_1inf tendsto_id
  have hRHS_int : Tendsto (fun R : ℝ ↦ ∫ t in (1 : ℝ)..R, Real.exp (-t) / t)
      atTop (𝓝 (∫ t in Ioi (1 : ℝ), Real.exp (-t) / t)) :=
    intervalIntegral_tendsto_integral_Ioi 1 (integrableOn_exp_neg_div_Ioi zero_lt_one) tendsto_id
  have hbdry : Tendsto (fun R : ℝ ↦ Real.log R * Real.exp (-R)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun R : ℝ ↦ R * Real.exp (-R)) atTop (𝓝 0) := by
      simpa only [pow_one] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    refine squeeze_zero' ?_ ?_ h0
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
      exact mul_nonneg (Real.log_nonneg hR) (Real.exp_pos _).le
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
      exact mul_le_mul_of_nonneg_right (Real.log_le_self (by linarith)) (Real.exp_pos _).le
  have hEq : (fun R : ℝ ↦ ∫ t in (1 : ℝ)..R, Real.log t * Real.exp (-t)) =ᶠ[atTop]
      fun R : ℝ ↦ -(Real.log R * Real.exp (-R)) + ∫ t in (1 : ℝ)..R, Real.exp (-t) / t := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    have hpos : ∀ t ∈ uIcc 1 R, 0 < t := fun t ht ↦ by
      rw [uIcc_of_le hR] at ht
      linarith [ht.1]
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (1 : ℝ)) (b := R)
      (u := fun t ↦ Real.log t) (u' := fun t ↦ t⁻¹)
      (v := fun t ↦ -Real.exp (-t)) (v' := fun t ↦ Real.exp (-t))
      (fun t ht ↦ Real.hasDerivAt_log (hpos t ht).ne')
      (fun t _ ↦ by
        have h := ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)).fun_neg
        simpa using h)
      (ContinuousOn.intervalIntegrable fun t ht ↦
        (continuousAt_inv₀ (hpos t ht).ne').continuousWithinAt)
      ((by fun_prop : Continuous fun t : ℝ ↦ Real.exp (-t)).intervalIntegrable 1 R)
    have hcomm : (∫ t in (1 : ℝ)..R, t⁻¹ * (-Real.exp (-t))) =
        -∫ t in (1 : ℝ)..R, Real.exp (-t) / t := by
      rw [← intervalIntegral.integral_neg]
      congr 1; ext t; ring
    rw [hcomm, Real.log_one, zero_mul, sub_zero] at hibp
    linarith
  exact tendsto_nhds_unique (hLHS.congr' hEq) (by simpa using hbdry.neg.add hRHS_int)

/-- **Integral representation of the Euler–Mascheroni constant:**
`γ = ∫ t in Ioc 0 1, (1 - exp (-t)) / t - ∫ t in Ioi 1, exp (-t) / t`. -/
theorem eulerMascheroniConstant_eq_integral_Ioc_sub_integral_Ioi :
    Real.eulerMascheroniConstant =
      (∫ t in Ioc (0 : ℝ) 1, (1 - Real.exp (-t)) / t) -
        ∫ t in Ioi (1 : ℝ), Real.exp (-t) / t := by
  have hint_01 : IntegrableOn (fun t : ℝ ↦ Real.log t * Real.exp (-t)) (Ioc 0 1) :=
    integrableOn_log_mul_exp_neg_Ioi.mono_set Ioc_subset_Ioi_self
  have hint_1inf : IntegrableOn (fun t : ℝ ↦ Real.log t * Real.exp (-t)) (Ioi 1) :=
    integrableOn_log_mul_exp_neg_Ioi.mono_set (Ioi_subset_Ioi zero_le_one)
  have hsplit : (∫ t in Ioi (0 : ℝ), Real.log t * Real.exp (-t)) =
      (∫ t in Ioc (0 : ℝ) 1, Real.log t * Real.exp (-t)) +
        ∫ t in Ioi (1 : ℝ), Real.log t * Real.exp (-t) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hint_01 hint_1inf]
  rw [Real.eulerMascheroniConstant_eq_neg_integral_log, hsplit,
    integral_Ioc_log_mul_exp_neg, integral_Ioi_log_mul_exp_neg]
  ring

/-! ### Definition and derivative of `li` -/

/-- The **unoffset logarithmic integral**
`li x = γ + log |log x| + ∑' n : ℕ, (log x) ^ (n + 1) / ((n + 1) * (n + 1)!)`.

Since Mathlib's `Real.log` satisfies `Real.log (-u) = Real.log u`, the formula agrees with the
classical exponential integral `Ei (log x)` for every `x > 0` with `x ≠ 1` (the value at `x = 1`
is the junk value `γ`). For `0 < x < 1` it equals `∫ t in 0..x, (log t)⁻¹`, and for `x > 1` it
equals the Cauchy principal value `lim_{ε → 0⁺} (∫_0^{1-ε} + ∫_{1+ε}^x) dt / log t`, satisfying
`Li x = li x - li 2`. -/
noncomputable def li (x : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (Real.log x) +
    ∑' n : ℕ, Real.log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ))

/-- Defining equation of `TauCeti.Real.li`. -/
theorem li_def (x : ℝ) :
    li x = Real.eulerMascheroniConstant + Real.log (Real.log x) +
      ∑' n : ℕ, Real.log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ)) :=
  (rfl)

/-- The exponential-integral form of `li (exp y)`. -/
theorem li_exp (y : ℝ) :
    li (Real.exp y) = Real.eulerMascheroniConstant + Real.log y +
      ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ)) := by
  simp only [li_def, Real.log_exp]

/-- The derivative of `li` at every `x > 0` with `x ≠ 1` is `(log x)⁻¹`. -/
theorem hasDerivAt_li {x : ℝ} (hx0 : 0 < x) (hx1 : x ≠ 1) :
    HasDerivAt li (Real.log x)⁻¹ x := by
  have hlog : Real.log x ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hx0 hx1
  let F : ℝ → ℝ := fun y ↦ Real.eulerMascheroniConstant + Real.log y +
    ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ))
  have hF : HasDerivAt F (Real.exp (Real.log x) / Real.log x) (Real.log x) := by
    have h1 := ((hasDerivAt_const (Real.log x) Real.eulerMascheroniConstant).fun_add
      (Real.hasDerivAt_log hlog)).fun_add (hasDerivAt_tsum_pow_div_mul_factorial (Real.log x))
    refine h1.congr_deriv ?_
    rw [dslope_of_ne _ hlog, slope_def_field, sub_zero, Real.exp_zero, zero_add]
    field_simp [hlog]
    ring
  have hcomp : HasDerivAt (fun t ↦ F (Real.log t))
      (Real.exp (Real.log x) / Real.log x * x⁻¹) x :=
    hF.comp x (Real.hasDerivAt_log hx0.ne')
  refine hcomp.congr_deriv ?_
  rw [Real.exp_log hx0]
  field_simp [hx0.ne', hlog]

/-- `li` is differentiable at every `x > 0` with `x ≠ 1`. -/
theorem differentiableAt_li {x : ℝ} (hx0 : 0 < x) (hx1 : x ≠ 1) :
    DifferentiableAt ℝ li x :=
  (hasDerivAt_li hx0 hx1).differentiableAt

/-- `li` is continuous at every `x > 0` with `x ≠ 1`. -/
theorem continuousAt_li {x : ℝ} (hx0 : 0 < x) (hx1 : x ≠ 1) :
    ContinuousAt li x :=
  (differentiableAt_li hx0 hx1).continuousAt

/-- `li` is differentiable on `(0, 1)`. -/
theorem differentiableOn_li_Ioo : DifferentiableOn ℝ li (Ioo 0 1) :=
  fun _ hx ↦ (differentiableAt_li hx.1 hx.2.ne).differentiableWithinAt

/-- `li` is differentiable on `(1, ∞)`. -/
theorem differentiableOn_li_Ioi : DifferentiableOn ℝ li (Ioi 1) :=
  fun _ hx ↦ (differentiableAt_li (zero_lt_one.trans hx) (ne_of_gt hx)).differentiableWithinAt

/-! ### Exponential integral representation and limit at `0⁺` -/

/-- For `z > 0`, `li (exp (-z)) = -∫ t in Ioi z, exp (-t) / t`. -/
theorem li_exp_neg_eq_neg_integral_Ioi {z : ℝ} (hz : 0 < z) :
    li (Real.exp (-z)) = -∫ t in Ioi z, Real.exp (-t) / t := by
  rw [li_exp, Real.log_neg_eq_log, ← integral_exp_sub_one_div_eq_tsum]
  have hneg : (∫ t in (0 : ℝ)..(-z), (Real.exp t - 1) / t) =
      -∫ t in (0 : ℝ)..z, (1 - Real.exp (-t)) / t := by
    have hcomp := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := z)
      (f := fun t : ℝ ↦ (Real.exp t - 1) / t)
    rw [neg_zero, intervalIntegral.integral_symm 0 (-z)] at hcomp
    have hfun : (fun t : ℝ ↦ (Real.exp (-t) - 1) / (-t)) =
        fun t : ℝ ↦ (1 - Real.exp (-t)) / t := by
      ext t; rw [div_neg, ← neg_div, neg_sub]
    rw [hfun] at hcomp
    linarith
  have hsplit : (∫ t in (0 : ℝ)..z, (1 - Real.exp (-t)) / t) =
      (∫ t in (0 : ℝ)..1, (1 - Real.exp (-t)) / t) +
        ∫ t in (1 : ℝ)..z, (1 - Real.exp (-t)) / t := by
    refine (intervalIntegral.integral_add_adjacent_intervals ?_ ?_).symm
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
        integrableOn_one_sub_exp_neg_div_Ioc
    · have hcont : ContinuousOn (fun t : ℝ ↦ (1 - Real.exp (-t)) / t) (uIcc 1 z) := by
        refine ContinuousOn.div (by fun_prop) continuousOn_id fun t ht ↦ ?_
        rcases mem_uIcc.mp ht with h | h
        · exact (zero_lt_one.trans_le h.1).ne'
        · exact (hz.trans_le h.1).ne'
      exact hcont.intervalIntegrable
  have h1z : (∫ t in (1 : ℝ)..z, (1 - Real.exp (-t)) / t) =
      Real.log z - ∫ t in (1 : ℝ)..z, Real.exp (-t) / t := by
    have hpos : ∀ t ∈ uIcc 1 z, 0 < t := fun t ht ↦ by
      rcases mem_uIcc.mp ht with h | h
      · exact zero_lt_one.trans_le h.1
      · exact hz.trans_le h.1
    have hinv : IntervalIntegrable (fun t : ℝ ↦ t⁻¹) volume 1 z :=
      ContinuousOn.intervalIntegrable fun t ht ↦
        (continuousAt_inv₀ (hpos t ht).ne').continuousWithinAt
    have hexp : IntervalIntegrable (fun t : ℝ ↦ Real.exp (-t) / t) volume 1 z :=
      ContinuousOn.intervalIntegrable <|
        ContinuousOn.div (by fun_prop) continuousOn_id fun t ht ↦ (hpos t ht).ne'
    have hsub : (fun t : ℝ ↦ (1 - Real.exp (-t)) / t) =
        fun t : ℝ ↦ t⁻¹ - Real.exp (-t) / t := by
      ext t; rw [sub_div, one_div]
    rw [hsub, intervalIntegral.integral_sub hinv hexp, integral_inv_of_pos zero_lt_one hz, div_one]
  have htail := intervalIntegral.integral_interval_add_Ioi
    (integrableOn_exp_neg_div_Ioi zero_lt_one) (integrableOn_exp_neg_div_Ioi hz)
  rw [hneg, hsplit, h1z, eulerMascheroniConstant_eq_integral_Ioc_sub_integral_Ioi,
    intervalIntegral.integral_of_le zero_le_one]
  linarith

/-- Exponential-integral representation for `y < 0`: `∫ u in Iic y, exp u / u = li (exp y)`. -/
theorem integral_Iic_exp_div_eq_li {y : ℝ} (hy : y < 0) :
    ∫ u in Iic y, Real.exp u / u = li (Real.exp y) := by
  have hneg : 0 < -y := neg_pos.mpr hy
  have hli := li_exp_neg_eq_neg_integral_Ioi hneg
  rw [neg_neg] at hli
  rw [hli]
  have hcomp := integral_comp_neg_Iic (c := y) (f := fun t : ℝ ↦ Real.exp (-t) / t)
  have hfun : (fun u : ℝ ↦ Real.exp u / u) = fun u : ℝ ↦ -(Real.exp (-(-u)) / (-u)) := by
    ext u; rw [neg_neg, div_neg, neg_neg]
  rw [hfun, integral_neg, hcomp]

/-- Exponential-integral Cauchy principal value for `y > 0`:
`lim_{ε → 0⁺} (∫ u in (-ε⁻¹)..(-ε), exp u / u + ∫ u in ε..y, exp u / u) = li (exp y)`. -/
theorem tendsto_pv_exp_div_eq_li {y : ℝ} (hy : 0 < y) :
    Tendsto
      (fun ε : ℝ ↦ (∫ u in (-ε⁻¹)..(-ε), Real.exp u / u) + ∫ u in ε..y, Real.exp u / u)
      (𝓝[>] 0) (𝓝 (li (Real.exp y))) := by
  -- Step 1: Take the `ε → 0⁺` limits of the three convergent pieces forming `li (exp y)`.
  have h1 : Tendsto (fun ε : ℝ ↦ ∫ t in ε..1, (1 - Real.exp (-t)) / t)
      (𝓝[>] 0) (𝓝 (∫ t in Ioc (0 : ℝ) 1, (1 - Real.exp (-t)) / t)) := by
    have hint : IntegrableOn (fun t : ℝ ↦ (1 - Real.exp (-t)) / t) (uIcc 0 1) := by
      rw [uIcc_of_le zero_le_one, integrableOn_Icc_iff_integrableOn_Ioc]
      exact integrableOn_one_sub_exp_neg_div_Ioc
    have hc := (intervalIntegral.continuousOn_primitive_interval_left (μ := volume) hint 0
      left_mem_uIcc).mono_of_mem_nhdsWithin
      (by rw [uIcc_of_le zero_le_one]; exact Icc_mem_nhdsGT zero_lt_one)
    simpa [intervalIntegral.integral_of_le zero_le_one] using hc.tendsto
  have h2 : Tendsto (fun ε : ℝ ↦ ∫ t in (1 : ℝ)..ε⁻¹, Real.exp (-t) / t)
      (𝓝[>] 0) (𝓝 (∫ t in Ioi (1 : ℝ), Real.exp (-t) / t)) :=
    intervalIntegral_tendsto_integral_Ioi 1 (integrableOn_exp_neg_div_Ioi zero_lt_one)
      tendsto_inv_nhdsGT_zero
  have h3 : Tendsto (fun ε : ℝ ↦ ∫ u in ε..y, (Real.exp u - 1) / u)
      (𝓝[>] 0) (𝓝 (∫ u in (0 : ℝ)..y, (Real.exp u - 1) / u)) := by
    have hint : IntegrableOn (fun u : ℝ ↦ (Real.exp u - 1) / u) (uIcc 0 y) := by
      rw [uIcc_of_le hy.le, integrableOn_Icc_iff_integrableOn_Ioc]
      refine (continuous_dslope_exp_zero.integrableOn_Ioc (a := 0) (b := y)).congr_fun
        (fun t ht ↦ ?_) measurableSet_Ioc
      rw [dslope_of_ne _ ht.1.ne', slope_def_field, sub_zero, Real.exp_zero]
    have hc := (intervalIntegral.continuousOn_primitive_interval_left (μ := volume) hint 0
      left_mem_uIcc).mono_of_mem_nhdsWithin
      (by rw [uIcc_of_le hy.le]; exact Icc_mem_nhdsGT hy)
    exact hc.tendsto
  have hsum : Tendsto
      (fun ε : ℝ ↦ (∫ t in ε..1, (1 - Real.exp (-t)) / t) -
        (∫ t in (1 : ℝ)..ε⁻¹, Real.exp (-t) / t) + Real.log y +
        ∫ u in ε..y, (Real.exp u - 1) / u)
      (𝓝[>] 0) (𝓝 (li (Real.exp y))) := by
    have h := ((h1.sub h2).add (tendsto_const_nhds (x := Real.log y))).add h3
    rwa [← eulerMascheroniConstant_eq_integral_Ioc_sub_integral_Ioi,
      integral_exp_sub_one_div_eq_tsum, ← li_exp] at h
  -- Step 2: For every `ε > 0`, rewrite the truncated principal value so the `log ε` terms cancel.
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hεinv : 0 < ε⁻¹ := inv_pos.mpr hε
  have hpos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : ∀ t ∈ uIcc a b, 0 < t := fun t ht ↦ by
    rcases mem_uIcc.mp ht with h | h
    · exact ha.trans_le h.1
    · exact hb.trans_le h.1
  have hint_exp {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
      IntervalIntegrable (fun t : ℝ ↦ Real.exp (-t) / t) volume a b :=
    ContinuousOn.intervalIntegrable <|
      ContinuousOn.div (by fun_prop) continuousOn_id fun t ht ↦ (hpos ha hb t ht).ne'
  have hint_inv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
      IntervalIntegrable (fun t : ℝ ↦ t⁻¹) volume a b :=
    ContinuousOn.intervalIntegrable fun t ht ↦
      (continuousAt_inv₀ (hpos ha hb t ht).ne').continuousWithinAt
  have hneg : (∫ u in (-ε⁻¹)..(-ε), Real.exp u / u) =
      -(∫ t in ε..1, Real.exp (-t) / t) - ∫ t in (1 : ℝ)..ε⁻¹, Real.exp (-t) / t := by
    have hcomp := intervalIntegral.integral_comp_neg (a := ε) (b := ε⁻¹)
      (f := fun u : ℝ ↦ Real.exp u / u)
    have hfun : (fun t : ℝ ↦ Real.exp (-t) / (-t)) = fun t : ℝ ↦ -(Real.exp (-t) / t) := by
      ext t; rw [div_neg]
    rw [hfun, intervalIntegral.integral_neg] at hcomp
    rw [← hcomp, ← intervalIntegral.integral_add_adjacent_intervals
      (hint_exp hε zero_lt_one) (hint_exp zero_lt_one hεinv)]
    ring
  have hpos_int : (∫ u in ε..y, Real.exp u / u) =
      Real.log y - Real.log ε + ∫ u in ε..y, (Real.exp u - 1) / u := by
    have hint_sub : IntervalIntegrable (fun u : ℝ ↦ (Real.exp u - 1) / u) volume ε y :=
      ContinuousOn.intervalIntegrable <|
        ContinuousOn.div (by fun_prop) continuousOn_id fun t ht ↦ (hpos hε hy t ht).ne'
    have hsplit : (fun u : ℝ ↦ Real.exp u / u) =
        fun u : ℝ ↦ u⁻¹ + (Real.exp u - 1) / u := by
      ext u; rw [← one_div, ← add_div]; ring
    rw [hsplit, intervalIntegral.integral_add (hint_inv hε hy) hint_sub,
      integral_inv_of_pos hε hy, Real.log_div hy.ne' hε.ne']
  have hε1 : (∫ t in ε..1, (1 - Real.exp (-t)) / t) =
      -Real.log ε - ∫ t in ε..1, Real.exp (-t) / t := by
    have hsub : (fun t : ℝ ↦ (1 - Real.exp (-t)) / t) =
        fun t : ℝ ↦ t⁻¹ - Real.exp (-t) / t := by
      ext t; rw [sub_div, one_div]
    rw [hsub, intervalIntegral.integral_sub (hint_inv hε zero_lt_one) (hint_exp hε zero_lt_one),
      integral_inv_of_pos hε zero_lt_one, one_div, Real.log_inv]
  linarith

/-- `li x → 0` as `x → 0⁺`. -/
theorem tendsto_li_nhdsGT_zero : Tendsto li (𝓝[>] 0) (𝓝 0) := by
  have hneg : Tendsto (fun x : ℝ ↦ -Real.log x) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hint_zero : Tendsto (fun x : ℝ ↦ ∫ t in Ioi (-Real.log x), Real.exp (-t) / t)
      (𝓝[>] 0) (𝓝 0) :=
    tendsto_integral_Ioi_zero hneg
  refine (hint_zero.neg.congr' ?_).trans (by rw [neg_zero])
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
  have hz : 0 < -Real.log x := neg_pos.mpr (Real.log_neg hx.1 hx.2)
  have hli := li_exp_neg_eq_neg_integral_Ioi hz
  rw [neg_neg, Real.exp_log hx.1] at hli
  exact hli.symm

/-! ### Offset identity, monotonicity, sign, and Soldner's constant -/

/-- **Offset identity**: for every `x > 1`, `Li x = li x - li 2`. -/
theorem logIntegral_eq_li_sub_li_two {x : ℝ} (hx : 1 < x) :
    logIntegral x = li x - li 2 := by
  rw [logIntegral_def]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht ↦ ?_) ?_
  · have ht1 : 1 < t := by
      rcases mem_uIcc.mp ht with h | h
      · exact one_lt_two.trans_le h.1
      · exact hx.trans_le h.1
    exact hasDerivAt_li (zero_lt_one.trans ht1) ht1.ne'
  · simpa only [pow_one] using intervalIntegrable_inv_log_pow 1 one_lt_two hx

/-- Equivalent form of the offset identity: for every `x > 1`, `li x = Li x + li 2`. -/
theorem li_eq_logIntegral_add_li_two {x : ℝ} (hx : 1 < x) :
    li x = logIntegral x + li 2 := by
  linarith [logIntegral_eq_li_sub_li_two hx]

/-- `li` is strictly decreasing on `(0, 1)`. -/
theorem strictAntiOn_li : StrictAntiOn li (Ioo 0 1) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioo 0 1)
    differentiableOn_li_Ioo.continuousOn fun x hx ↦ ?_
  rw [interior_Ioo] at hx
  rw [(hasDerivAt_li hx.1 hx.2.ne).deriv]
  exact inv_lt_zero.mpr (Real.log_neg hx.1 hx.2)

/-- `li x < 0` for every `0 < x < 1`. -/
theorem li_neg_of_lt_one {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : li x < 0 := by
  have hz : 0 < -Real.log x := neg_pos.mpr (Real.log_neg hx0 hx1)
  have hli := li_exp_neg_eq_neg_integral_Ioi hz
  rw [neg_neg, Real.exp_log hx0] at hli
  rw [hli, neg_lt_zero]
  have hpos : 0 < ∫ t in (-Real.log x)..(-Real.log x + 1), Real.exp (-t) / t := by
    refine intervalIntegral.integral_pos (by linarith) ?_ (fun t ht ↦ ?_)
      ⟨-Real.log x, ⟨le_rfl, by linarith⟩, div_pos (Real.exp_pos _) hz⟩
    · exact ContinuousOn.div (by fun_prop) continuousOn_id fun t ht ↦
        (hz.trans_le ht.1).ne'
    · exact div_nonneg (Real.exp_pos _).le (hz.trans ht.1).le
  have hnn : 0 ≤ ∫ t in Ioi (-Real.log x + 1), Real.exp (-t) / t :=
    setIntegral_nonneg measurableSet_Ioi fun t ht ↦
      div_nonneg (Real.exp_pos _).le (by linarith [hz, mem_Ioi.mp ht])
  have hadd := intervalIntegral.integral_interval_add_Ioi
    (integrableOn_exp_neg_div_Ioi hz)
    (integrableOn_exp_neg_div_Ioi (by linarith : 0 < -Real.log x + 1))
  linarith

/-- `li` is strictly increasing on `(1, ∞)`. -/
theorem strictMonoOn_li : StrictMonoOn li (Ioi 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 1)
    differentiableOn_li_Ioi.continuousOn fun x hx ↦ ?_
  rw [interior_Ioi] at hx
  rw [(hasDerivAt_li (zero_lt_one.trans hx) (ne_of_gt hx)).deriv]
  exact inv_pos.mpr (Real.log_pos hx)

/-- `li x → -∞` as `x → 1⁺`. -/
theorem tendsto_li_nhdsGT_one : Tendsto li (𝓝[>] 1) atBot := by
  have hlog : Tendsto Real.log (𝓝[>] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((Real.continuousAt_log one_ne_zero).tendsto.mono_left nhdsWithin_le_nhds |>.trans
        (by rw [Real.log_one])) ?_
    filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
    exact Real.log_pos hx
  have hloglog : Tendsto (fun x : ℝ ↦ Real.log (Real.log x)) (𝓝[>] 1) atBot :=
    Real.tendsto_log_nhdsGT_zero.comp hlog
  have hS : Tendsto
      (fun x : ℝ ↦ Real.eulerMascheroniConstant +
        ∑' n : ℕ, Real.log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ)))
      (𝓝[>] 1) (𝓝 Real.eulerMascheroniConstant) := by
    have hSc : Continuous (fun y : ℝ ↦
        ∑' n : ℕ, y ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ))) :=
      continuous_iff_continuousAt.mpr fun y ↦ (hasDerivAt_tsum_pow_div_mul_factorial y).continuousAt
    have h0 : (∑' n : ℕ, (0 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ))) = 0 := by
      simp [zero_pow (Nat.succ_ne_zero _)]
    have h1 : Tendsto (fun x : ℝ ↦
        ∑' n : ℕ, Real.log x ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ)))
        (𝓝[>] 1) (𝓝 0) := by
      simpa only [Function.comp_def, h0] using
        (hSc.continuousAt (x := (0 : ℝ))).tendsto.comp (hlog.mono_right nhdsWithin_le_nhds)
    simpa only [add_zero] using (tendsto_const_nhds (x := Real.eulerMascheroniConstant)).add h1
  have htot := hS.add_atBot hloglog
  refine htot.congr fun x ↦ ?_
  simp only [li_def]
  ring

/-- `li x → +∞` as `x → +∞`. -/
theorem tendsto_li_atTop : Tendsto li atTop atTop := by
  have hLi : Tendsto logIntegral atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_
      (tendsto_div_log_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with x hx
    have hlog : 0 < Real.log x := Real.log_pos (by linarith)
    have h1 : 1 / 2 * (x / Real.log x) ≤ (x - 2) / Real.log x := by
      rw [mul_div_assoc', div_le_div_iff_of_pos_right hlog]
      linarith
    exact h1.trans (le_logIntegral (by linarith))
  refine (hLi.atTop_add (tendsto_const_nhds (x := li 2))).congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  exact (li_eq_logIntegral_add_li_two hx).symm

/-- `li x > 0` for every `x ≥ 3 / 2`. -/
theorem li_pos_of_three_halves_le {x : ℝ} (hx : 3 / 2 ≤ x) : 0 < li x := by
  suffices h32 : 0 < li (3 / 2) by
    rcases hx.eq_or_lt with rfl | hlt
    · exact h32
    · exact h32.trans
        (strictMonoOn_li (by norm_num : (1 : ℝ) < 3 / 2) (by linarith : (1 : ℝ) < x) hlt)
  -- Enclose `log (3 / 2) = log 3 - log 2` from Mathlib's 9-digit bounds.
  have hl2_hi : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hl3_lo : 1.0986122885 < Real.log 3 := Real.log_three_gt_d9
  have hlog32 : Real.log (3 / 2) = Real.log 3 - Real.log 2 :=
    Real.log_div (by norm_num) (by norm_num)
  have hy_lo : (0.405465 : ℝ) < Real.log (3 / 2) := by rw [hlog32]; linarith
  have hy_pos : 0 < Real.log (3 / 2) := by linarith
  -- Lower bound `log (log (3 / 2)) = -1 + log (e * log (3 / 2))` via `2 u / (u + 2) < log (1 + u)`.
  have he_lo : 2.7182818283 < Real.exp 1 := Real.exp_one_gt_d9
  have hprod : 1.1021 < Real.exp 1 * Real.log (3 / 2) := by nlinarith
  have hlog_prod : (0.0971 : ℝ) < Real.log (Real.exp 1 * Real.log (3 / 2)) := by
    have hlt := Real.lt_log_one_add_of_pos (x := Real.exp 1 * Real.log (3 / 2) - 1) (by linarith)
    rw [add_sub_cancel] at hlt
    have hrat : (0.0971 : ℝ) < 2 * (Real.exp 1 * Real.log (3 / 2) - 1) /
        (Real.exp 1 * Real.log (3 / 2) - 1 + 2) := by
      rw [lt_div_iff₀ (by linarith)]
      linarith
    exact hrat.trans hlt
  have hloglog : (-0.9029 : ℝ) < Real.log (Real.log (3 / 2)) := by
    have hmul : Real.log (Real.exp 1 * Real.log (3 / 2)) = 1 + Real.log (Real.log (3 / 2)) := by
      rw [Real.log_mul (Real.exp_pos 1).ne' hy_pos.ne', Real.log_exp]
    linarith
  -- Keep the first two positive terms of the series.
  have hseries : (0.4465 : ℝ) <
      ∑' n : ℕ, Real.log (3 / 2) ^ (n + 1) / (((n : ℝ) + 1) * ((n + 1).factorial : ℝ)) := by
    have hle := (summable_pow_div_mul_factorial (Real.log (3 / 2))).sum_le_tsum
      (Finset.range 2) (fun n _ ↦ by positivity)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.factorial_one, pow_one, zero_add, mul_one, div_one] at hle
    norm_num at hle
    nlinarith
  rw [li_def]
  linarith [Real.one_half_lt_eulerMascheroniConstant]

/-- **Soldner's constant**: `li` has a unique zero in `(1, ∞)`. -/
theorem existsUnique_li_eq_zero : ∃! μ ∈ Ioi (1 : ℝ), li μ = 0 := by
  have hcont : ContinuousOn li (Ioi 1) := differentiableOn_li_Ioi.continuousOn
  obtain ⟨a, ha1, ha_neg⟩ : ∃ a : ℝ, 1 < a ∧ li a < 0 := by
    have hev := (tendsto_li_nhdsGT_one.eventually (eventually_lt_atBot (0 : ℝ))).and
      self_mem_nhdsWithin
    obtain ⟨a, ha_neg, ha1⟩ := hev.exists
    exact ⟨a, ha1, ha_neg⟩
  have hb_pos : 0 < li (3 / 2) := li_pos_of_three_halves_le le_rfl
  have hab : a < 3 / 2 := by
    by_contra h
    push Not at h
    linarith [li_pos_of_three_halves_le h]
  have h0_mem : (0 : ℝ) ∈ Icc (li a) (li (3 / 2)) := ⟨ha_neg.le, hb_pos.le⟩
  obtain ⟨μ, hμ_mem, hμ_eq⟩ := intermediate_value_Icc hab.le
    (hcont.mono fun t ht ↦ ha1.trans_le ht.1) h0_mem
  refine ⟨μ, ⟨ha1.trans_le hμ_mem.1, hμ_eq⟩, fun y hy ↦ ?_⟩
  exact strictMonoOn_li.injOn hy.1 (ha1.trans_le hμ_mem.1) (hy.2.trans hμ_eq.symm)

end TauCeti.Real
