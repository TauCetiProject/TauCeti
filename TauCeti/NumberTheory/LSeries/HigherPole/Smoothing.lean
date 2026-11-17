/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Basic

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.SpecialFunctions.Integrals.SincSq

/-!
# Squared-sinc smoothing kernel and Delange's polynomial weight

This file defines the two analytic building blocks of Delange's Tauberian method for higher-order
poles (Delange 1954, §§3.1–3.4):

* `TauCeti.HigherPoleTauberian.squaredSinc`: the normalised squared-sinc kernel
  `K_λ(v) = (λ / π) sinc (λ v)²`, a probability density on `ℝ` whose Fourier transform is a
  compactly supported triangle on `[-2λ, 2λ]`, together with its total mass, Fourier representation,
  cosine transform, quantitative tail bound, and mass concentration on `[-h, h]`.
* `TauCeti.HigherPoleTauberian.delangeWeight`: Delange's polynomial regularising weight
  `w_k(t) = t ∫₀¹ exp (-u t) u ^ k / k! du`, together with its global Erlang identity, relation to
  `TauCeti.regularizedGamma`, positivity, asymptotic normalisation `w_k(t) t ^ k → 1`, uniform shift
  limit `w_k(t + h) / w_k(t) → 1`, smoothness, explicit derivatives, and vanishing logarithmic
  derivative `w_k'(t) / w_k(t) → 0`.

## References

* H. Delange, *Généralisation du théorème de Ikehara*, Ann. Sci. École Norm. Sup. (3) **71**
  (1954), 213–242, especially §§3.1–3.4.
-/

public section

noncomputable section

open Filter MeasureTheory Real Set
open scoped ContDiff Topology

namespace TauCeti.HigherPoleTauberian

/-! ### The normalised squared-sinc kernel -/

/-- The normalised squared-sinc kernel `K_λ(v) = (λ / π) sinc (λ v)²`. For `λ > 0` it is a
probability density on `ℝ` whose Fourier transform in angular frequency is the triangular tent
`1 - |y| / (2λ)` supported on `[-2λ, 2λ]` (Delange 1954, §3.3.5, p. 226). -/
def squaredSinc (ell v : ℝ) : ℝ :=
  ell / π * sinc (ell * v) ^ 2

/-- Definitional unfolding of `squaredSinc`. -/
theorem squaredSinc_def (ell v : ℝ) :
    squaredSinc ell v = ell / π * sinc (ell * v) ^ 2 := by
  rfl

/-- At the origin, `squaredSinc ell 0 = ell / π`. -/
@[simp]
theorem squaredSinc_zero (ell : ℝ) : squaredSinc ell 0 = ell / π := by
  simp [squaredSinc]

/-- At bandwidth `0`, the squared-sinc kernel vanishes identically. -/
@[simp]
theorem squaredSinc_zero_left (v : ℝ) : squaredSinc 0 v = 0 := by
  simp [squaredSinc]

/-- The squared-sinc kernel is even in its spatial argument. -/
@[simp]
theorem squaredSinc_neg (ell v : ℝ) : squaredSinc ell (-v) = squaredSinc ell v := by
  simp [squaredSinc, mul_neg, sinc_neg]

/-- For every real `ell`, the kernel vanishes at `π / ell` (the first positive zero when
`0 < ell`). -/
@[simp]
theorem squaredSinc_pi_div (ell : ℝ) : squaredSinc ell (π / ell) = 0 := by
  rcases eq_or_ne ell 0 with rfl | hell
  · simp
  · rw [squaredSinc, mul_div_cancel₀ _ hell, sinc_of_ne_zero pi_pos.ne', sin_pi]
    simp

/-- For `0 ≤ ell`, the squared-sinc kernel is nonnegative everywhere. -/
theorem squaredSinc_nonneg {ell : ℝ} (hell : 0 ≤ ell) (v : ℝ) : 0 ≤ squaredSinc ell v :=
  mul_nonneg (div_nonneg hell pi_pos.le) (sq_nonneg _)

/-- For `0 ≤ ell`, the squared-sinc kernel is bounded above by `ell / π`. -/
theorem squaredSinc_le {ell : ℝ} (hell : 0 ≤ ell) (v : ℝ) : squaredSinc ell v ≤ ell / π := by
  have h1 : sinc (ell * v) ^ 2 ≤ 1 := by nlinarith [abs_le.mp (abs_sinc_le_one (ell * v))]
  calc squaredSinc ell v = ell / π * sinc (ell * v) ^ 2 := rfl
    _ ≤ ell / π * 1 := mul_le_mul_of_nonneg_left h1 (div_nonneg hell pi_pos.le)
    _ = ell / π := mul_one _

/-- Inverse-square tail bound for `squaredSinc`: for `0 ≤ ell` and `v ≠ 0`,
`squaredSinc ell v ≤ (π * ell * v ^ 2)⁻¹`. -/
theorem squaredSinc_le_inv_mul_sq {ell v : ℝ} (hell : 0 ≤ ell) (hv : v ≠ 0) :
    squaredSinc ell v ≤ (π * ell * v ^ 2)⁻¹ := by
  rcases hell.eq_or_lt with rfl | hell
  · simp
  have hmul : ell * v ≠ 0 := mul_ne_zero hell.ne' hv
  rw [squaredSinc, sinc_of_ne_zero hmul, div_pow]
  have hsin : sin (ell * v) ^ 2 ≤ 1 := sin_sq_le_one (ell * v)
  calc ell / π * (sin (ell * v) ^ 2 / (ell * v) ^ 2)
      ≤ ell / π * (1 / (ell * v) ^ 2) := by
        gcongr
    _ = (π * ell * v ^ 2)⁻¹ := by
        field_simp [hell.ne', hv, pi_pos.ne']

/-- The squared-sinc kernel is continuous for every real bandwidth `ell`. -/
@[fun_prop]
theorem continuous_squaredSinc (ell : ℝ) : Continuous (squaredSinc ell) := by
  unfold squaredSinc
  fun_prop

/-- The squared-sinc kernel is Lebesgue integrable on `ℝ` for every real bandwidth `ell`. -/
theorem integrable_squaredSinc (ell : ℝ) : Integrable (squaredSinc ell) := by
  rcases eq_or_ne ell 0 with rfl | hell
  · have hzero : squaredSinc 0 = 0 := funext squaredSinc_zero_left
    rw [hzero]
    exact integrable_zero ℝ ℝ volume
  · exact (TauCeti.integrable_sinc_sq.comp_mul_left' hell).const_mul (ell / π)

/-- For every `0 < ell`, the squared-sinc kernel is a probability density on `ℝ`. -/
theorem squaredSinc_mass {ell : ℝ} (hell : 0 < ell) : ∫ v : ℝ, squaredSinc ell v = 1 := by
  simp only [squaredSinc]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun x : ℝ ↦ sinc x ^ 2) ell,
    abs_inv, abs_of_pos hell, smul_eq_mul, TauCeti.integral_sinc_sq]
  field_simp [hell.ne', pi_pos.ne']

/-- Fourier representation of the squared-sinc kernel in angular frequency: for `0 ≤ ell`,
`squaredSinc ell v` is the inverse Fourier transform of the triangular tent
`1 - |y| / (2 * ell)` supported on `[-2 * ell, 2 * ell]`. -/
theorem squaredSinc_fourier {ell : ℝ} (hell : 0 ≤ ell) (v : ℝ) :
    (squaredSinc ell v : ℂ) = 1 / (2 * π) *
      ∫ y : ℝ in (-(2 * ell))..(2 * ell),
        ((1 - |y| / (2 * ell) : ℝ) : ℂ) * Complex.exp (Complex.I * y * v) := by
  rw [TauCeti.integral_one_sub_abs_div_mul_cexp (by linarith : 0 ≤ 2 * ell) v]
  have harg : 2 * ell * v / 2 = ell * v := by ring
  rw [harg, squaredSinc]
  push_cast
  field_simp [pi_pos.ne']

/-- Cosine transform of the squared-sinc kernel:
`∫ v, squaredSinc ell v * cos (ξ * v) = max (1 - |ξ| / (2 * ell)) 0` for `0 < ell`.
In particular it vanishes whenever `2 * ell ≤ |ξ|`. -/
theorem integral_squaredSinc_mul_cos {ell : ℝ} (hell : 0 < ell) (ξ : ℝ) :
    ∫ v : ℝ, squaredSinc ell v * cos (ξ * v) = max (1 - |ξ| / (2 * ell)) 0 := by
  have hrew : (fun v : ℝ ↦ squaredSinc ell v * cos (ξ * v)) =
      fun v ↦ (ell / π) * (sinc (ell * v) ^ 2 * cos ((ξ / ell) * (ell * v))) := funext fun v ↦ by
    rw [squaredSinc, ← mul_assoc (ξ / ell), div_mul_cancel₀ _ hell.ne']
    ring
  have habs : |ξ / ell| / 2 = |ξ| / (2 * ell) := by
    rw [abs_div, abs_of_pos hell, div_div, mul_comm ell 2]
  rw [hrew, integral_const_mul,
    Measure.integral_comp_mul_left (fun x : ℝ ↦ sinc x ^ 2 * cos ((ξ / ell) * x)) ell,
    abs_inv, abs_of_pos hell, smul_eq_mul, TauCeti.integral_sinc_sq_mul_cos, habs]
  field_simp [hell.ne', pi_pos.ne']

/-- Quantitative tail bound for the squared-sinc kernel: for `0 ≤ ell` and `0 < h`,
`∫ v in {v | h ≤ |v|}, squaredSinc ell v ≤ 2 / (π * ell * h)`. -/
theorem integral_squaredSinc_tail_le {ell h : ℝ} (hell : 0 ≤ ell) (hh : 0 < h) :
    ∫ v in {v : ℝ | h ≤ |v|}, squaredSinc ell v ≤ 2 / (π * ell * h) := by
  rcases hell.eq_or_lt with rfl | hell
  · simp [squaredSinc_zero_left]
  have hmeas : MeasurableSet {v : ℝ | h ≤ |v|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hsym : ∫ v in {v : ℝ | h ≤ |v|}, squaredSinc ell v =
      2 * ∫ v in Ioi h, squaredSinc ell v := by
    rw [← integral_indicator hmeas]
    have hcomp := integral_comp_abs (f := fun v : ℝ ↦ (Ici h).indicator (squaredSinc ell) v)
    have heq : (fun v : ℝ ↦ ({v : ℝ | h ≤ |v|}).indicator (squaredSinc ell) v) =
        fun v : ℝ ↦ (Ici h).indicator (squaredSinc ell) |v| := funext fun v ↦ by
      by_cases hv : h ≤ |v|
      · have hv1 : v ∈ {v : ℝ | h ≤ |v|} := hv
        have hv2 : |v| ∈ Ici h := hv
        rw [Set.indicator_of_mem hv1, Set.indicator_of_mem hv2]
        rcases le_total 0 v with h0 | h0
        · rw [abs_of_nonneg h0]
        · rw [abs_of_nonpos h0, squaredSinc_neg]
      · have hv1 : v ∉ {v : ℝ | h ≤ |v|} := hv
        have hv2 : |v| ∉ Ici h := hv
        rw [Set.indicator_of_notMem hv1, Set.indicator_of_notMem hv2]
    rw [heq, hcomp, integral_indicator measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici,
      Set.inter_eq_left.mpr (Ici_subset_Ioi.mpr hh), integral_Ici_eq_integral_Ioi]
  rw [hsym]
  have hint_rpow : IntegrableOn (fun v : ℝ ↦ (π * ell)⁻¹ * v ^ (-2 : ℝ)) (Ioi h) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hh).const_mul _
  have hle : ∫ v in Ioi h, squaredSinc ell v ≤ ∫ v in Ioi h, (π * ell)⁻¹ * v ^ (-2 : ℝ) := by
    refine setIntegral_mono_on (integrable_squaredSinc ell).integrableOn hint_rpow
      measurableSet_Ioi fun v hv ↦ ?_
    have hv0 : 0 < v := hh.trans hv
    have hrpow : (π * ell)⁻¹ * v ^ (-2 : ℝ) = (π * ell * v ^ 2)⁻¹ := by
      rw [rpow_neg hv0.le, rpow_two]
      ring
    rw [hrpow]
    exact squaredSinc_le_inv_mul_sq hell.le hv0.ne'
  have hrpow_val : ∫ v in Ioi h, (π * ell)⁻¹ * v ^ (-2 : ℝ) = (π * ell * h)⁻¹ := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hh]
    have hadd : (-2 : ℝ) + 1 = -1 := by norm_num
    rw [hadd, rpow_neg_one]
    field_simp [pi_pos.ne', hell.ne', hh.ne']
  calc 2 * ∫ v in Ioi h, squaredSinc ell v
      ≤ 2 * (π * ell * h)⁻¹ := by linarith [hle, hrpow_val]
    _ = 2 / (π * ell * h) := by ring

/-- Tail concentration of `squaredSinc`: for every `0 < h`, the mass outside `(-h, h)` vanishes
as the bandwidth tends to infinity. -/
theorem tendsto_integral_squaredSinc_tail {h : ℝ} (hh : 0 < h) :
    Tendsto (fun ell : ℝ ↦ ∫ v in {v : ℝ | h ≤ |v|}, squaredSinc ell v) atTop (𝓝 0) := by
  have hupper : Tendsto (fun ell : ℝ ↦ 2 / (π * ell * h)) atTop (𝓝 0) := by
    have hmul : Tendsto (fun ell : ℝ ↦ π * ell * h) atTop atTop :=
      (tendsto_id.const_mul_atTop pi_pos).atTop_mul_const hh
    exact tendsto_const_nhds.div_atTop hmul
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with ell hell
    exact setIntegral_nonneg (measurableSet_le measurable_const continuous_abs.measurable)
      fun v _ ↦ squaredSinc_nonneg hell.le v
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with ell hell
    exact integral_squaredSinc_tail_le hell.le hh

/-- Mass concentration of `squaredSinc`: for every `0 < h`, the mass inside `[-h, h]` tends to
`1` as the bandwidth tends to infinity. -/
theorem tendsto_integral_squaredSinc_Icc {h : ℝ} (hh : 0 < h) :
    Tendsto (fun ell : ℝ ↦ ∫ v in Icc (-h) h, squaredSinc ell v) atTop (𝓝 1) := by
  have hcompl_lim :
      Tendsto (fun ell : ℝ ↦ ∫ v in (Icc (-h) h)ᶜ, squaredSinc ell v) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ (tendsto_integral_squaredSinc_tail hh)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with ell hell
      exact setIntegral_nonneg measurableSet_Icc.compl fun v _ ↦ squaredSinc_nonneg hell.le v
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with ell hell
      refine setIntegral_mono_set (integrable_squaredSinc ell).integrableOn
        (ae_of_all _ fun v ↦ squaredSinc_nonneg hell.le v) (ae_of_all _ fun v hv ↦ ?_)
      rw [mem_compl_iff, mem_Icc, not_and_or, not_le, not_le] at hv
      rcases hv with h1 | h2
      · exact le_trans (by linarith) (neg_le_abs v)
      · exact le_trans h2.le (le_abs_self v)
  have hsub : Tendsto (fun ell : ℝ ↦ (1 : ℝ) - ∫ v in (Icc (-h) h)ᶜ, squaredSinc ell v)
      atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub hcompl_lim
  rw [sub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ell hell
  have hsplit := integral_add_compl (s := Icc (-h) h) measurableSet_Icc (integrable_squaredSinc ell)
  rw [squaredSinc_mass hell] at hsplit
  linarith

/-! ### Delange's polynomial weight -/

/-- The unscaled Laplace integral `I_k(t) = ∫₀¹ exp (-u t) u ^ k / k! du` underlying
`delangeWeight`. -/
private def delangeIntegral (k : ℕ) (t : ℝ) : ℝ :=
  ∫ u : ℝ in (0 : ℝ)..1, exp (-u * t) * u ^ k / (k.factorial : ℝ)

/-- Delange's regularising polynomial weight
`w_k(t) = t ∫₀¹ exp (-u t) u ^ k / k! du` (Delange 1954, §§3.1–3.2 and §5.2.1). It vanishes at
`0`, is positive for `t > 0`, satisfies `w_k(t) t ^ k = P(k + 1, t)` for `t ≥ 0` (the regularised
lower incomplete gamma function), and is asymptotic to `t ^ (-k)` as `t → ∞`. -/
def delangeWeight (k : ℕ) (t : ℝ) : ℝ :=
  t * ∫ u : ℝ in (0 : ℝ)..1, exp (-u * t) * u ^ k / (k.factorial : ℝ)

/-- Definitional unfolding of `delangeWeight`. -/
theorem delangeWeight_def (k : ℕ) (t : ℝ) :
    delangeWeight k t = t * ∫ u : ℝ in (0 : ℝ)..1, exp (-u * t) * u ^ k / (k.factorial : ℝ) := by
  rfl

/-- Delange's weight vanishes at `t = 0`. -/
@[simp]
theorem delangeWeight_zero (k : ℕ) : delangeWeight k 0 = 0 := by
  simp [delangeWeight]

/-- For `k = 0`, `delangeWeight 0 t = 1 - exp (-t)` for every real `t`. -/
@[simp]
theorem delangeWeight_zero_left (t : ℝ) : delangeWeight 0 t = 1 - exp (-t) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · rw [delangeWeight]
    have hderiv : ∀ u ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun x : ℝ ↦ -(exp (-x * t) / t))
          (exp (-u * t) * u ^ 0 / ((0 : ℕ).factorial : ℝ)) u := by
      intro u _
      have h1 : HasDerivAt (fun x : ℝ ↦ -x * t) (-t) u := by
        simpa using (hasDerivAt_id' u).neg.mul_const t
      convert (h1.exp.div_const t).neg using 1
      simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one]
      field_simp [ht]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((by fun_prop : Continuous _).intervalIntegrable 0 1)]
    simp only [neg_zero, zero_mul, exp_zero, neg_mul, one_mul]
    field_simp [ht]
    ring

/-- Global recurrence for Delange's weight, valid for every real `t`:
`t * w_{k + 1}(t) = w_k(t) - t * exp (-t) / (k + 1)!`. -/
theorem mul_delangeWeight_succ (k : ℕ) (t : ℝ) :
    t * delangeWeight (k + 1) t =
      delangeWeight k t - t * exp (-t) / ((k + 1).factorial : ℝ) := by
  let F : ℝ → ℝ := fun u ↦ -(exp (-u * t) * u ^ (k + 1) / ((k + 1).factorial : ℝ))
  have hderiv : ∀ u ∈ uIcc (0 : ℝ) 1,
      HasDerivAt F
        (t * (exp (-u * t) * u ^ (k + 1) / ((k + 1).factorial : ℝ)) -
          exp (-u * t) * u ^ k / (k.factorial : ℝ)) u := by
    intro u _
    have h1 : HasDerivAt (fun x : ℝ ↦ exp (-x * t)) (exp (-u * t) * (-t)) u := by
      simpa using ((hasDerivAt_id' u).neg.mul_const t).exp
    have h2 : HasDerivAt (fun x : ℝ ↦ x ^ (k + 1)) (((k + 1 : ℕ) : ℝ) * u ^ k) u := by
      simpa using hasDerivAt_pow (k + 1) u
    convert ((h1.mul h2).div_const ((k + 1).factorial : ℝ)).neg using 1
    rw [Nat.factorial_succ, Nat.cast_mul]
    have hfac : ((k.factorial : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hsucc : ((k + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    field_simp [hfac, hsucc]
    ring
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous _).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_sub ((by fun_prop : Continuous _).intervalIntegrable 0 1)
    ((by fun_prop : Continuous _).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul] at hint
  have hF1 : F 1 = -(exp (-t) / ((k + 1).factorial : ℝ)) := by
    simp [F]
  have hF0 : F 0 = 0 := by
    simp [F, zero_pow (Nat.succ_ne_zero k)]
  rw [hF1, hF0, sub_zero] at hint
  have hmul := congrArg (fun x : ℝ ↦ t * x) hint
  rw [mul_sub, mul_neg, ← mul_div_assoc] at hmul
  simp only [delangeWeight] at *
  linarith

/-- Global Erlang identity for Delange's weight, valid for every real `t`:
`w_k(t) * t ^ k = 1 - exp (-t) * ∑ j < k + 1, t ^ j / j!`. -/
theorem delangeWeight_mul_pow_eq (k : ℕ) (t : ℝ) :
    delangeWeight k t * t ^ k =
      1 - exp (-t) * ∑ j ∈ Finset.range (k + 1), t ^ j / (j.factorial : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpow : delangeWeight (k + 1) t * t ^ (k + 1) = (t * delangeWeight (k + 1) t) * t ^ k := by
      ring
    rw [hpow, mul_delangeWeight_succ, sub_mul, ih,
      Finset.sum_range_succ (fun j ↦ t ^ j / (j.factorial : ℝ)) (k + 1), mul_add]
    have hterm : t * exp (-t) / ((k + 1).factorial : ℝ) * t ^ k =
        exp (-t) * (t ^ (k + 1) / ((k + 1).factorial : ℝ)) := by ring
    linarith

/-- On `[0, ∞)`, `delangeWeight k t * t ^ k` is the regularised lower incomplete gamma function
`P(k + 1, t)`. -/
theorem delangeWeight_mul_pow_eq_regularizedGamma (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    delangeWeight k t * t ^ k = TauCeti.regularizedGamma (k + 1) t := by
  rw [delangeWeight_mul_pow_eq]
  have h := TauCeti.regularizedGamma_natCast (n := k + 1) (Nat.succ_ne_zero k) ht
  simpa only [Nat.cast_add, Nat.cast_one] using h.symm

/-- Delange's weight is nonnegative on `[0, ∞)`. -/
theorem delangeWeight_nonneg (k : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ delangeWeight k t := by
  rw [delangeWeight]
  exact mul_nonneg ht (intervalIntegral.integral_nonneg zero_le_one fun u hu ↦ by
    have hu0 : 0 ≤ u := hu.1
    positivity)

/-- Delange's weight is strictly positive on `(0, ∞)`. -/
theorem delangeWeight_pos (k : ℕ) {t : ℝ} (ht : 0 < t) : 0 < delangeWeight k t := by
  have hpos : 0 < delangeWeight k t * t ^ k := by
    rw [delangeWeight_mul_pow_eq_regularizedGamma k ht.le]
    exact TauCeti.regularizedGamma_pos (by positivity) ht
  exact pos_of_mul_pos_left hpos (pow_nonneg ht.le k)

/-- For `0 ≤ t`, the normalised weight `delangeWeight k t * t ^ k` is at most `1`. -/
theorem delangeWeight_mul_pow_le_one (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    delangeWeight k t * t ^ k ≤ 1 := by
  rw [delangeWeight_mul_pow_eq_regularizedGamma k ht]
  exact TauCeti.regularizedGamma_le_one _ _

/-- Asymptotic normalisation of Delange's weight: `w_k(t) * t ^ k → 1` as `t → ∞`. -/
theorem delangeWeight_normalization (k : ℕ) :
    Tendsto (fun t : ℝ ↦ delangeWeight k t * t ^ k) atTop (𝓝 1) := by
  refine (TauCeti.tendsto_regularizedGamma_atTop (s := (k : ℝ) + 1) (by positivity)).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact (delangeWeight_mul_pow_eq_regularizedGamma k ht).symm

/-- Pointwise two-sided bound on `w_k(t + h) / w_k(t)` for `|h| ≤ H₀ < t`, obtained from
monotonicity of `u ↦ w_k(u) u ^ k = P(k + 1, u)`. -/
private theorem delangeWeight_div_bounds (k : ℕ) {t h H₀ : ℝ}
    (hH₀ : 0 ≤ H₀) (ht : H₀ < t) (hh : |h| ≤ H₀) :
    (delangeWeight k (t - H₀) * (t - H₀) ^ k) / (delangeWeight k t * t ^ k) * (t / (t + H₀)) ^ k ≤
        delangeWeight k (t + h) / delangeWeight k t ∧
      delangeWeight k (t + h) / delangeWeight k t ≤
        (delangeWeight k (t + H₀) * (t + H₀) ^ k) / (delangeWeight k t * t ^ k) *
          (t / (t - H₀)) ^ k := by
  let P : ℝ → ℝ := fun u ↦ delangeWeight k u * u ^ k
  have ht_pos : 0 < t := lt_of_le_of_lt hH₀ ht
  have htm_pos : 0 < t - H₀ := sub_pos.mpr ht
  have hth_pos : 0 < t + h := by linarith [(abs_le.mp hh).1]
  have htp_pos : 0 < t + H₀ := by linarith
  have hPt_pos : 0 < P t := mul_pos (delangeWeight_pos k ht_pos) (pow_pos ht_pos k)
  have hP_lo : P (t - H₀) ≤ P (t + h) := by
    simp only [P, delangeWeight_mul_pow_eq_regularizedGamma k htm_pos.le,
      delangeWeight_mul_pow_eq_regularizedGamma k hth_pos.le]
    exact TauCeti.regularizedGamma_monotone _ (by linarith [(abs_le.mp hh).1])
  have hP_hi : P (t + h) ≤ P (t + H₀) := by
    simp only [P, delangeWeight_mul_pow_eq_regularizedGamma k hth_pos.le,
      delangeWeight_mul_pow_eq_regularizedGamma k htp_pos.le]
    exact TauCeti.regularizedGamma_monotone _ (by linarith [(abs_le.mp hh).2])
  have hfac : delangeWeight k (t + h) / delangeWeight k t =
      P (t + h) / P t * (t / (t + h)) ^ k := by
    simp only [P, div_pow]
    field_simp [(delangeWeight_pos k ht_pos).ne', ht_pos.ne', hth_pos.ne']
  rw [hfac]
  refine ⟨?_, ?_⟩
  · have hdiv : P (t - H₀) / P t ≤ P (t + h) / P t := div_le_div_of_nonneg_right hP_lo hPt_pos.le
    have hpow : (t / (t + H₀)) ^ k ≤ (t / (t + h)) ^ k := pow_le_pow_left₀ (by positivity)
      (div_le_div_of_nonneg_left ht_pos.le hth_pos (by linarith [(abs_le.mp hh).2])) k
    have hPth : 0 ≤ P (t + h) :=
      mul_nonneg (delangeWeight_nonneg k hth_pos.le) (pow_nonneg hth_pos.le k)
    exact mul_le_mul hdiv hpow (by positivity) (div_nonneg hPth hPt_pos.le)
  · have hdiv : P (t + h) / P t ≤ P (t + H₀) / P t := div_le_div_of_nonneg_right hP_hi hPt_pos.le
    have hpow : (t / (t + h)) ^ k ≤ (t / (t - H₀)) ^ k := pow_le_pow_left₀ (by positivity)
      (div_le_div_of_nonneg_left ht_pos.le htm_pos (by linarith [(abs_le.mp hh).1])) k
    have hPtp : 0 ≤ P (t + H₀) :=
      mul_nonneg (delangeWeight_nonneg k htp_pos.le) (pow_nonneg htp_pos.le k)
    exact mul_le_mul hdiv hpow (by positivity) (div_nonneg hPtp hPt_pos.le)

/-- Uniform slow variation of Delange's weight: for every real `H` and `0 < ε`, eventually as
`t → ∞`, `|w_k(t + h) / w_k(t) - 1| < ε` holds uniformly for all `|h| ≤ H`. -/
theorem eventually_abs_delangeWeight_div_sub_one_lt (k : ℕ) (H : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ h : ℝ, |h| ≤ H →
      |delangeWeight k (t + h) / delangeWeight k t - 1| < ε := by
  let H₀ : ℝ := max H 0
  have hH₀ : 0 ≤ H₀ := le_max_right H 0
  let P : ℝ → ℝ := fun u ↦ delangeWeight k u * u ^ k
  have hP : Tendsto P atTop (𝓝 1) := delangeWeight_normalization k
  have hlow_lim : Tendsto (fun t : ℝ ↦ P (t - H₀) / P t * (t / (t + H₀)) ^ k) atTop (𝓝 1) := by
    have h1 := (hP.comp (tendsto_id.atTop_add (tendsto_const_nhds (x := -H₀)))).div hP one_ne_zero
    have hrat : Tendsto (fun t : ℝ ↦ t / (t + H₀)) atTop (𝓝 1) := by
      simpa only [add_zero] using TauCeti.tendsto_add_div_add_atTop (0 : ℝ) H₀
    simpa [sub_eq_add_neg] using h1.mul (hrat.pow k)
  have hhigh_lim : Tendsto (fun t : ℝ ↦ P (t + H₀) / P t * (t / (t - H₀)) ^ k) atTop (𝓝 1) := by
    have h1 := (hP.comp (tendsto_id.atTop_add (tendsto_const_nhds (x := H₀)))).div hP one_ne_zero
    have hrat : Tendsto (fun t : ℝ ↦ t / (t - H₀)) atTop (𝓝 1) := by
      simpa only [add_zero, sub_eq_add_neg] using TauCeti.tendsto_add_div_add_atTop (0 : ℝ) (-H₀)
    simpa [sub_eq_add_neg] using h1.mul (hrat.pow k)
  filter_upwards [eventually_gt_atTop H₀,
    hlow_lim.eventually (Ioi_mem_nhds (by linarith : 1 - ε < 1)),
    hhigh_lim.eventually (Iio_mem_nhds (by linarith : (1 : ℝ) < 1 + ε))] with t ht hlow hhigh
  intro h hh
  have ⟨hlo, hhi⟩ := delangeWeight_div_bounds k hH₀ ht (hh.trans (le_max_left H 0))
  rw [abs_sub_lt_iff]
  constructor <;> linarith

/-- Pointwise shift limit of Delange's weight: for every real `h`,
`w_k(t + h) / w_k(t) → 1` as `t → ∞`. -/
theorem delangeWeight_shift (k : ℕ) (h : ℝ) :
    Tendsto (fun t : ℝ ↦ delangeWeight k (t + h) / delangeWeight k t) atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_abs_delangeWeight_div_sub_one_lt k |h| hε)
  exact ⟨T, fun t ht ↦ hT t ht h le_rfl⟩

/-- Uniform bound on the `x`-derivative of the integrand of `delangeIntegral k` for `u ∈ (0, 1]`
and `x ∈ Metric.ball t 1`. -/
private theorem norm_deriv_delangeIntegrand_le (k : ℕ) {t x u : ℝ}
    (hu : u ∈ Ioc (0 : ℝ) 1) (hx : x ∈ Metric.ball t 1) :
    ‖(-u) * exp (-u * x) * u ^ k / (k.factorial : ℝ)‖ ≤ exp (|t| + 1) := by
  have hu0 : 0 ≤ u := hu.1.le
  have hu1 : u ≤ 1 := hu.2
  have hxabs : |x| ≤ |t| + 1 := by
    rw [Metric.mem_ball, Real.dist_eq] at hx
    linarith [abs_sub_abs_le_abs_sub x t]
  have hexp : exp (-u * x) ≤ exp (|t| + 1) := by
    apply exp_le_exp.mpr
    calc -u * x ≤ |-u * x| := le_abs_self _
      _ = u * |x| := by rw [abs_mul, abs_neg, abs_of_nonneg hu0]
      _ ≤ 1 * (|t| + 1) := mul_le_mul hu1 hxabs (abs_nonneg x) zero_le_one
      _ = |t| + 1 := one_mul _
  have hfac1 : (1 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hupow : u * u ^ k ≤ 1 := by
    calc u * u ^ k ≤ 1 * 1 ^ k :=
          mul_le_mul hu1 (pow_le_pow_left₀ hu0 hu1 k) (pow_nonneg hu0 k) zero_le_one
      _ = 1 := by ring
  have hrew : (-u) * exp (-u * x) * u ^ k / (k.factorial : ℝ) =
      -(u * u ^ k * exp (-u * x) / (k.factorial : ℝ)) := by ring
  rw [Real.norm_eq_abs, hrew, abs_neg, abs_of_nonneg (by positivity)]
  calc u * u ^ k * exp (-u * x) / (k.factorial : ℝ)
      ≤ u * u ^ k * exp (-u * x) := div_le_self (by positivity) hfac1
    _ ≤ 1 * exp (|t| + 1) := mul_le_mul hupow hexp (exp_pos _).le zero_le_one
    _ = exp (|t| + 1) := one_mul _

/-- Derivative of the auxiliary integral `delangeIntegral k`:
`(delangeIntegral k)'(t) = -(k + 1) * delangeIntegral (k + 1) t`. -/
private theorem hasDerivAt_delangeIntegral (k : ℕ) (t : ℝ) :
    HasDerivAt (delangeIntegral k) (-(k + 1 : ℝ) * delangeIntegral (k + 1) t) t := by
  let F : ℝ → ℝ → ℝ := fun x u ↦ exp (-u * x) * u ^ k / (k.factorial : ℝ)
  let F' : ℝ → ℝ → ℝ := fun x u ↦ (-u) * exp (-u * x) * u ^ k / (k.factorial : ℝ)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := (0 : ℝ)) (b := 1) (F := F) (F' := F') (bound := fun _ ↦ exp (|t| + 1))
    (Metric.ball_mem_nhds t zero_lt_one)
    (Eventually.of_forall fun x ↦ (by fun_prop : Continuous (F x)).aestronglyMeasurable)
    ((by fun_prop : Continuous (F t)).intervalIntegrable 0 1)
    (by fun_prop : Continuous (F' t)).aestronglyMeasurable
    (ae_of_all _ fun u hu x hx ↦
      norm_deriv_delangeIntegrand_le k (uIoc_of_le (zero_le_one (α := ℝ)) ▸ hu) hx)
    (intervalIntegrable_const)
    (ae_of_all _ fun u _ x _ ↦ by
      have hexp : HasDerivAt (fun y : ℝ ↦ exp (-u * y)) (exp (-u * x) * (-u)) x := by
        simpa using ((hasDerivAt_id' x).const_mul (-u)).exp
      convert (hexp.mul_const (u ^ k)).div_const (k.factorial : ℝ) using 1
      simp only [F']
      ring)
  have hval : ∫ u in (0 : ℝ)..1, F' t u = -(k + 1 : ℝ) * delangeIntegral (k + 1) t := by
    rw [delangeIntegral, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ ↦ ?_
    simp only [F', Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hfac : ((k.factorial : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hsucc : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hfac, hsucc]
    ring
  have hfun : (fun x ↦ ∫ u in (0 : ℝ)..1, F x u) = delangeIntegral k := rfl
  rw [hfun, hval] at h
  exact h.2

/-- The auxiliary integral `delangeIntegral k` is smooth on `ℝ`. -/
private theorem contDiff_delangeIntegral (k : ℕ) : ContDiff ℝ ∞ (delangeIntegral k) := by
  rw [contDiff_infty]
  intro n
  induction n generalizing k with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.mpr fun t ↦ (hasDerivAt_delangeIntegral k t).continuousAt
  | succ n ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_deriv]
    refine ⟨fun t ↦ (hasDerivAt_delangeIntegral k t).differentiableAt, fun h ↦ by simp at h, ?_⟩
    have hderiv : deriv (delangeIntegral k) = fun t ↦ -(k + 1 : ℝ) * delangeIntegral (k + 1) t :=
      funext fun t ↦ (hasDerivAt_delangeIntegral k t).deriv
    rw [hderiv]
    exact contDiff_const.mul (ih (k + 1))

/-- Derivative of Delange's weight at every real `t`. -/
theorem hasDerivAt_delangeWeight (k : ℕ) (t : ℝ) :
    HasDerivAt (delangeWeight k)
      ((∫ u : ℝ in (0 : ℝ)..1, exp (-u * t) * u ^ k / (k.factorial : ℝ)) -
        (k + 1 : ℝ) * delangeWeight (k + 1) t) t := by
  have hfun : delangeWeight k = fun x ↦ x * delangeIntegral k x := rfl
  rw [hfun]
  convert (hasDerivAt_id' t).mul (hasDerivAt_delangeIntegral k t) using 1
  simp only [delangeWeight, delangeIntegral]
  ring

/-- Delange's weight is smooth (`C^∞`) on `ℝ`. -/
@[fun_prop]
theorem contDiff_delangeWeight (k : ℕ) : ContDiff ℝ ∞ (delangeWeight k) :=
  contDiff_id.mul (contDiff_delangeIntegral k)

/-- Delange's weight is continuous on `ℝ`. -/
@[fun_prop]
theorem continuous_delangeWeight (k : ℕ) : Continuous (delangeWeight k) :=
  (contDiff_delangeWeight k).continuous

/-- Delange's weight is differentiable on `ℝ`. -/
@[fun_prop]
theorem differentiable_delangeWeight (k : ℕ) : Differentiable ℝ (delangeWeight k) :=
  fun t ↦ (hasDerivAt_delangeWeight k t).differentiableAt

/-- At the origin, `w_k'(0) = 1 / (k + 1)!`. -/
@[simp]
theorem deriv_delangeWeight_zero (k : ℕ) :
    deriv (delangeWeight k) 0 = ((k + 1).factorial : ℝ)⁻¹ := by
  rw [(hasDerivAt_delangeWeight k 0).deriv, delangeWeight_zero, mul_zero, sub_zero]
  simp only [mul_zero, exp_zero, one_mul, intervalIntegral.integral_div, integral_pow, one_pow,
    zero_pow (Nat.succ_ne_zero k), sub_zero, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k), (by positivity : (k : ℝ) + 1 ≠ 0)]

/-- Away from `0`, `w_k'(t) = exp (-t) / k! - k * w_k(t) / t`. -/
theorem deriv_delangeWeight_of_ne_zero (k : ℕ) {t : ℝ} (ht : t ≠ 0) :
    deriv (delangeWeight k) t = exp (-t) / (k.factorial : ℝ) - k * delangeWeight k t / t := by
  rw [(hasDerivAt_delangeWeight k t).deriv]
  have hrec := mul_delangeWeight_succ k t
  have hI : t * (∫ u : ℝ in (0 : ℝ)..1, exp (-u * t) * u ^ k / (k.factorial : ℝ)) =
      delangeWeight k t := rfl
  have hmul : t * ((∫ u : ℝ in (0 : ℝ)..1, exp (-u * t) * u ^ k / (k.factorial : ℝ)) -
      (k + 1 : ℝ) * delangeWeight (k + 1) t) =
      t * (exp (-t) / (k.factorial : ℝ) - k * delangeWeight k t / t) := by
    have h1 : t * ((k + 1 : ℝ) * delangeWeight (k + 1) t) =
        (k + 1 : ℝ) * (t * delangeWeight (k + 1) t) := by ring
    rw [mul_sub, hI, h1, hrec, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hfac : ((k.factorial : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hsucc : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp [ht, hfac, hsucc]
    ring
  exact mul_left_cancel₀ ht hmul

/-- The logarithmic derivative of Delange's weight vanishes at infinity:
`w_k'(t) / w_k(t) → 0` as `t → ∞`. -/
theorem tendsto_deriv_delangeWeight_div (k : ℕ) :
    Tendsto (fun t : ℝ ↦ deriv (delangeWeight k) t / delangeWeight k t) atTop (𝓝 0) := by
  have hnum : Tendsto (fun t : ℝ ↦ t ^ k * exp (-t) / (k.factorial : ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_mul_exp_neg_atTop_nhds_zero k).div_const (k.factorial : ℝ)
  have h1 : Tendsto (fun t : ℝ ↦
      (t ^ k * exp (-t) / (k.factorial : ℝ)) / (delangeWeight k t * t ^ k) - (k : ℝ) / t)
      atTop (𝓝 (0 / 1 - 0)) :=
    (hnum.div (delangeWeight_normalization k) one_ne_zero).sub
      (tendsto_const_nhds.div_atTop tendsto_id)
  simp only [zero_div, sub_zero] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [deriv_delangeWeight_of_ne_zero k ht.ne']
  have hw : delangeWeight k t ≠ 0 := (delangeWeight_pos k ht).ne'
  field_simp [ht.ne', hw]

end TauCeti.HigherPoleTauberian
