/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.SpecialFunctions.Erf.Series
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Hermite.Bound
import TauCeti.RingTheory.Polynomial.Hermite.GeneratingFunction

/-!
# Laplace–Hermite generating series and the rotational addition theorem

Through the Laplace integral representation of the parabolic cylinder function `U(a, z)` for
`Re(a + 1 / 2) > 0` (DLMF 12.5.1, with `s = a + 1 / 2`) and the Hermite specialization
`U(-m - 1 / 2, y) = exp(-y² / 4) He_m(y)` (DLMF 12.7.2), the rotational addition theorem
(DLMF 12.13.5, including the `(cos t)^{-a - 1 / 2}` factor required by the Hermite cases) reduces on
the half-plane `0 < Re s` to interchanging a Hermite generating series with the Gaussian–Laplace
moment integral

  `I(s, z) = ∫ u in Ioi (0 : ℝ), u ^ (s - 1) * exp(-u² / 2 - z * u)`

and extending `M`-shifted tails in `s` across `Re s ≤ 0` by holomorphy on `{s : ℂ | 0 < Re s + M}`.

This file develops the analytic theory of `I(s, z)` and of the Hermite-weighted Laplace series
`∑_{m ≥ 0} (-w)^m / m! * He_m(y) * I(s + m, z)` in both the interior disk `‖w‖ < 1` (covering
`w = tan t` for `|t| < π / 4`) and the boundary circle `‖w‖ ≤ 1` (covering the endpoint
`t = π / 4`, where `tan(π / 4) = 1`), together with the general Abel limit as `r → 1⁻` via
`t = arctan r`.

## Main results

* `TauCeti.integrableOn_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi_iff`,
  `TauCeti.differentiable_integral_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi`,
  `TauCeti.differentiableOn_integral_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi`,
  `TauCeti.integral_cpow_mul_cexp_neg_div_sq_div_two_sub_mul_Ioi`: exact integrability criterion
  (`0 < Re s`), entirety in `z` (for every `s : ℂ`), holomorphy in `s` on `{0 < Re s}`, and
  positive rescaling of `I(s, z)`.
* `TauCeti.norm_pow_div_factorial_mul_hermite_mul_integral_le`: termwise Gaussian–half-Gamma
  majorant from `TauCeti.abs_aeval_hermite_mul_exp_div_factorial_le`.
* `TauCeti.summable_norm_pow_div_factorial_mul_hermite_mul_integral_of_norm_lt_one`,
  `TauCeti.summable_norm_pow_div_factorial_mul_hermite_mul_integral_of_re_pos`,
  `TauCeti.summable_norm_pow_div_factorial_mul_hermite_mul_integral_of_re_neg`: absolute
  summability for all `s : ℂ` when `‖w‖ < 1` or (`‖w‖ ≤ 1` and `0 < Re z`), and for `Re s < 0`
  when `‖w‖ ≤ 1` and `0 ≤ Re z`.
* `TauCeti.differentiableOn_tsum_pow_div_factorial_mul_hermite_mul_integral_add_of_norm_lt_one`,
  `TauCeti.differentiableOn_tsum_div_factorial_mul_hermite_mul_integral_add_of_re_pos`:
  holomorphy of the `M`-shifted tail in `s` on `{s : ℂ | 0 < Re s + M}` for `‖w‖ < 1` and at the
  unit-circle endpoint `w = 1` when `0 < Re z`.
* `TauCeti.hasSum_pow_div_factorial_mul_hermite_mul_integral_of_norm_lt_one`,
  `TauCeti.hasSum_pow_div_factorial_mul_hermite_mul_integral_of_re_pos`,
  `TauCeti.hasSum_tan_pow_div_factorial_mul_hermite_mul_integral`,
  `TauCeti.hasSum_tan_pow_div_factorial_mul_hermite_mul_integral_of_re_pos`,
  `TauCeti.hasSum_rotational_addition_laplaceHermite`,
  `TauCeti.hasSum_rotational_addition_laplaceHermite_of_re_pos`: exact `HasSum` evaluations of the
  generating series and the DLMF 12.13.5 normalized rotational addition series for `|t| < π / 4`
  and (when `0 < Re z`) on the closed interval `|t| ≤ π / 4`.
* `TauCeti.tendsto_abel_laplaceHermite`, `TauCeti.tendsto_abel_rotational_addition_laplaceHermite`:
  endpoint Abel limit as `r → 1⁻` for `0 < Re s` and every `z : ℂ`, `y : ℝ`.

## References

* *NIST Digital Library of Mathematical Functions*, [§12.5](https://dlmf.nist.gov/12.5),
  [§12.7](https://dlmf.nist.gov/12.7), and [§12.13](https://dlmf.nist.gov/12.13#E5).
-/

public section

open Complex Real MeasureTheory Set Filter Polynomial
open scoped Nat Topology

namespace TauCeti

/-! ### Gaussian–Laplace moment integrals on `(0, ∞)` -/

/-- Norm of the general Gaussian–Laplace integrand `u^{s - 1} exp(-q u² - z u)` for `u > 0`. -/
private theorem norm_cpow_mul_cexp_neg_mul_sq_sub_mul (s q z : ℂ) {u : ℝ} (hu : 0 < u) :
    ‖(u : ℂ) ^ (s - 1) * cexp (-q * (u : ℂ) ^ 2 - z * u)‖ =
      u ^ (s.re - 1) * rexp (-q.re * u ^ 2 - z.re * u) := by
  have hre : (-q * (u : ℂ) ^ 2 - z * u).re = -q.re * u ^ 2 - z.re * u := by
    simp [← Complex.ofReal_pow]
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.norm_exp, Complex.sub_re,
    Complex.one_re, hre]

/-- Norm of the standard Gaussian–Laplace integrand `u^{s - 1} exp(-u² / 2 - z u)` for `u > 0`. -/
private theorem norm_cpow_mul_cexp_neg_sq_div_two_sub_mul (s z : ℂ) {u : ℝ} (hu : 0 < u) :
    ‖(u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u)‖ =
      u ^ (s.re - 1) * rexp (-u ^ 2 / 2 - z.re * u) := by
  have h := norm_cpow_mul_cexp_neg_mul_sq_sub_mul s (1 / 2) z hu
  have hq : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
  rwa [hq, show -(1 / 2 : ℂ) * (u : ℂ) ^ 2 = -(u : ℂ) ^ 2 / 2 by ring,
    show -(1 / 2 : ℝ) * u ^ 2 = -u ^ 2 / 2 by ring] at h

/-- For `0 < Re s`, `0 < Re q`, and every `z : ℂ`, the Gaussian–Laplace moment kernel
`u ↦ u^{s - 1} exp(-q u² - z u)` is integrable on `(0, ∞)`. -/
theorem integrableOn_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi {s q : ℂ} (hs : 0 < s.re)
    (hq : 0 < q.re) (z : ℂ) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (s - 1) * cexp (-q * (u : ℂ) ^ 2 - z * u)) (Ioi 0) := by
  have hgauss : IntegrableOn (fun u : ℝ => u ^ (s.re - 1) * rexp (-(q.re / 2) * u ^ 2)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq (by positivity) (by linarith)
  refine (hgauss.const_mul (rexp (z.re ^ 2 / (2 * q.re)))).mono'
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [norm_cpow_mul_cexp_neg_mul_sq_sub_mul s q z hu]
  have hsq : -q.re * u ^ 2 - z.re * u ≤ -(q.re / 2) * u ^ 2 + z.re ^ 2 / (2 * q.re) := by
    rw [← sub_nonneg]
    have hident : -(q.re / 2) * u ^ 2 + z.re ^ 2 / (2 * q.re) - (-q.re * u ^ 2 - z.re * u) =
        (q.re * u + z.re) ^ 2 / (2 * q.re) := by field_simp; ring
    rw [hident]
    positivity
  calc u ^ (s.re - 1) * rexp (-q.re * u ^ 2 - z.re * u)
      ≤ u ^ (s.re - 1) * rexp (-(q.re / 2) * u ^ 2 + z.re ^ 2 / (2 * q.re)) := by
        gcongr
        exact (Real.rpow_pos_of_pos hu _).le
    _ = rexp (z.re ^ 2 / (2 * q.re)) * (u ^ (s.re - 1) * rexp (-(q.re / 2) * u ^ 2)) := by
        rw [Real.exp_add]; ring

/-- For `0 < Re s` and every `z : ℂ`, `u ↦ u^{s - 1} exp(-u² / 2 - z u)` is integrable on
`(0, ∞)`. -/
theorem integrableOn_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi {s : ℂ} (hs : 0 < s.re) (z : ℂ) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u)) (Ioi 0) := by
  refine (integrableOn_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi hs
    (q := 1 / 2) (by norm_num) z).congr_fun (fun u _ => ?_) measurableSet_Ioi
  ring_nf

/-- Real-valued counterpart of `integrableOn_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi`: for
`0 < σ` and every `b : ℝ`, `u ↦ u^{σ - 1} exp(-u² / 2 - b u)` is integrable on `(0, ∞)`. -/
private theorem integrableOn_rpow_mul_rexp_neg_sq_div_two_sub_mul_Ioi {σ : ℝ} (hσ : 0 < σ)
    (b : ℝ) :
    IntegrableOn (fun u : ℝ => u ^ (σ - 1) * rexp (-u ^ 2 / 2 - b * u)) (Ioi 0) := by
  have h : IntegrableOn
      (fun u : ℝ => ‖(u : ℂ) ^ ((σ : ℂ) - 1) * cexp (-(u : ℂ) ^ 2 / 2 - (b : ℂ) * u)‖) (Ioi 0) :=
    (integrableOn_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi (s := (σ : ℂ)) (by simpa using hσ)
      (b : ℂ)).norm
  refine h.congr_fun (fun u hu => ?_) measurableSet_Ioi
  simpa using norm_cpow_mul_cexp_neg_sq_div_two_sub_mul (σ : ℂ) (b : ℂ) hu

/-- The standard Gaussian–Laplace moment kernel `u ↦ u^{s - 1} exp(-u² / 2 - z u)` is integrable
on `(0, ∞)` if and only if `0 < Re s` (independently of `z : ℂ`). -/
@[simp]
theorem integrableOn_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi_iff {s z : ℂ} :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u)) (Ioi 0) ↔
      0 < s.re := by
  refine ⟨fun h => ?_, fun hs => integrableOn_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi hs z⟩
  have hIoo : IntegrableOn
      (fun u : ℝ => ‖(u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u)‖) (Ioo 0 1) :=
    (h.mono_set Ioo_subset_Ioi_self).norm
  set c := rexp (-1 / 2 - |z.re|)
  have hc : 0 < c := Real.exp_pos _
  have hrpow : IntegrableOn (fun u : ℝ => c * u ^ (s.re - 1)) (Ioo 0 1) := by
    refine hIoo.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hu0 : 0 < u := hu.1
    rw [Real.norm_of_nonneg (mul_nonneg hc.le (Real.rpow_pos_of_pos hu0 _).le),
      norm_cpow_mul_cexp_neg_sq_div_two_sub_mul s z hu0, mul_comm c]
    have hu2 : u ^ 2 ≤ 1 := by nlinarith [hu.1, hu.2]
    have hzu : -|z.re| ≤ -z.re * u := by
      have h1 : z.re * u ≤ |z.re| :=
        (le_abs_self _).trans
          (by rw [abs_mul, abs_of_pos hu0]; nlinarith [hu.2, abs_nonneg z.re])
      linarith
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
      (Real.rpow_pos_of_pos hu0 _).le
  have hiff := (intervalIntegral.integrableOn_Ioo_rpow_iff (s := s.re - 1) zero_lt_one).mp
    (IntegrableOn.congr_fun (hrpow.const_mul c⁻¹) (fun u _ => by field_simp) measurableSet_Ioo)
  linarith

/-- For every `s : ℂ` (with no restriction on `Re s`), the Gaussian–Laplace integral
`z ↦ ∫₀^∞ u^{s - 1} exp(-u² / 2 - z u) du` is entire on `ℂ`: for `0 < Re s` by differentiation
under the integral sign, and for `Re s ≤ 0` because the Bochner integral vanishes identically. -/
theorem differentiable_integral_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi (s : ℂ) :
    Differentiable ℂ fun z : ℂ =>
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u) := by
  by_cases hs : 0 < s.re
  · intro z₀
    have hball : Metric.ball z₀ 1 ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ zero_lt_one
    have hbint : IntegrableOn
        (fun u : ℝ => u ^ s.re * rexp (-u ^ 2 / 2 + (‖z₀‖ + 1) * u)) (Ioi 0) := by
      refine (integrableOn_rpow_mul_rexp_neg_sq_div_two_sub_mul_Ioi (σ := s.re + 1) (by linarith)
        (-(‖z₀‖ + 1))).congr_fun (fun u _ => ?_) measurableSet_Ioi
      ring_nf
    have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Ioi (0 : ℝ)))
      (F := fun z (u : ℝ) => (u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u))
      (F' := fun z (u : ℝ) => (u : ℂ) ^ (s - 1) * (cexp (-(u : ℂ) ^ 2 / 2 - z * u) * -(u : ℂ)))
      (bound := fun u : ℝ => u ^ s.re * rexp (-u ^ 2 / 2 + (‖z₀‖ + 1) * u))
      hball (Eventually.of_forall fun _ => Measurable.aestronglyMeasurable (by fun_prop))
      (integrableOn_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi hs z₀)
      (Measurable.aestronglyMeasurable (by fun_prop)) ?_ hbint ?_
    · exact h.2.differentiableAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu z hz
      have hu' : 0 < u := hu
      have hz_re : -z.re ≤ ‖z₀‖ + 1 := by
        have hdist : ‖z - z₀‖ < 1 := by simpa [dist_eq_norm] using hz
        have hnorm_z : ‖z‖ < ‖z₀‖ + 1 := by linarith [norm_sub_rev z z₀, norm_sub_norm_le z z₀]
        linarith [abs_re_le_norm z, neg_le_abs z.re]
      rw [← mul_assoc, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hu'.le,
        norm_cpow_mul_cexp_neg_sq_div_two_sub_mul s z hu', mul_right_comm,
        ← Real.rpow_add_one hu'.ne', sub_add_cancel]
      gcongr
      nlinarith
    · filter_upwards with u z _
      have hd : HasDerivAt (fun w : ℂ => -(u : ℂ) ^ 2 / 2 - w * u) (-(u : ℂ)) z := by
        simpa using ((hasDerivAt_id z).mul_const (u : ℂ)).const_sub (-(u : ℂ) ^ 2 / 2)
      exact hd.cexp.const_mul ((u : ℂ) ^ (s - 1))
  · have hzero : (fun z : ℂ =>
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u)) = 0 := by
      ext z
      exact integral_undef (mt integrableOn_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi_iff.mp hs)
    rw [hzero]
    exact differentiable_const 0

/-- Two-power algebraic bound on `|log u| * u^{σ - 1}` for `u > 0` and `0 < δ ≤ σ ≤ R`, avoiding
any indicator split at `u = 1`. -/
private theorem abs_log_mul_rpow_le {u δ σ R : ℝ} (hu : 0 < u) (hδ : 0 < δ) (hδσ : δ ≤ σ)
    (hσR : σ ≤ R) :
    |Real.log u| * u ^ (σ - 1) ≤ 2 / δ * u ^ (δ / 2 - 1) + u ^ R := by
  rcases le_or_gt u 1 with hu1 | hu1
  · have hlog_nonpos : Real.log u ≤ 0 := Real.log_nonpos hu.le hu1
    have hpow_le : u ^ (σ - 1) ≤ u ^ (δ - 1) :=
      Real.rpow_le_rpow_of_exponent_ge hu hu1 (by linarith)
    have hlog_bound : -Real.log u ≤ 2 / δ * u ^ (-δ / 2) := by
      have hx : 0 < u ^ (-δ / 2) := Real.rpow_pos_of_pos hu _
      have hlogx : Real.log (u ^ (-δ / 2)) ≤ u ^ (-δ / 2) :=
        (Real.log_le_sub_one_of_pos hx).trans (by linarith)
      rw [Real.log_rpow hu] at hlogx
      calc -Real.log u
          = 2 / δ * (-δ / 2 * Real.log u) := by field_simp
        _ ≤ 2 / δ * u ^ (-δ / 2) := mul_le_mul_of_nonneg_left hlogx (by positivity)
    have h1 : |Real.log u| * u ^ (σ - 1) ≤ 2 / δ * u ^ (δ / 2 - 1) := by
      rw [abs_of_nonpos hlog_nonpos]
      calc -Real.log u * u ^ (σ - 1)
          ≤ (2 / δ * u ^ (-δ / 2)) * u ^ (δ - 1) :=
            mul_le_mul hlog_bound hpow_le (by positivity) (by positivity)
        _ = 2 / δ * (u ^ (-δ / 2) * u ^ (δ - 1)) := by ring
        _ = 2 / δ * u ^ (δ / 2 - 1) := by
            rw [← Real.rpow_add hu]; congr 2; ring
    have hrpos : 0 ≤ u ^ R := (Real.rpow_pos_of_pos hu R).le
    exact h1.trans (le_add_of_nonneg_right hrpos)
  · have hlog_nonneg : 0 ≤ Real.log u := Real.log_nonneg hu1.le
    have hlog_le : Real.log u ≤ u := (Real.log_le_sub_one_of_pos hu).trans (by linarith)
    have hpow_le : u ^ (σ - 1) ≤ u ^ (R - 1) :=
      Real.rpow_le_rpow_of_exponent_le hu1.le (by linarith)
    have h2 : |Real.log u| * u ^ (σ - 1) ≤ u ^ R := by
      rw [abs_of_nonneg hlog_nonneg]
      calc Real.log u * u ^ (σ - 1)
          ≤ u * u ^ (R - 1) := mul_le_mul hlog_le hpow_le (by positivity) hu.le
        _ = u ^ R := by rw [mul_comm, ← Real.rpow_add_one hu.ne', sub_add_cancel]
    have hpos1 : 0 ≤ 2 / δ * u ^ (δ / 2 - 1) := by positivity
    exact h2.trans (le_add_of_nonneg_left hpos1)

/-- For every `z : ℂ`, the Gaussian–Laplace integral
`s ↦ ∫₀^∞ u^{s - 1} exp(-u² / 2 - z u) du` is holomorphic on `{s : ℂ | 0 < Re s}`. -/
theorem differentiableOn_integral_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi (z : ℂ) :
    DifferentiableOn ℂ
      (fun s : ℂ => ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u))
      {s : ℂ | 0 < s.re} := by
  intro s₀ hs₀
  have hs₀' : 0 < s₀.re := hs₀
  set δ := s₀.re / 2 with hδ_def
  have hδ : 0 < δ := by positivity
  have hball : Metric.ball s₀ δ ∈ 𝓝 s₀ := Metric.ball_mem_nhds s₀ hδ
  have hb1 : IntegrableOn
      (fun u : ℝ => 2 / δ * (u ^ (δ / 2 - 1) * rexp (-u ^ 2 / 2 - z.re * u))) (Ioi 0) :=
    (integrableOn_rpow_mul_rexp_neg_sq_div_two_sub_mul_Ioi (σ := δ / 2) (by positivity)
      z.re).const_mul (2 / δ)
  have hb2 : IntegrableOn
      (fun u : ℝ => u ^ (2 * s₀.re) * rexp (-u ^ 2 / 2 - z.re * u)) (Ioi 0) := by
    refine (integrableOn_rpow_mul_rexp_neg_sq_div_two_sub_mul_Ioi (σ := 2 * s₀.re + 1)
      (by positivity) z.re).congr_fun (fun u _ => ?_) measurableSet_Ioi
    ring_nf
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun s (u : ℝ) => (u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u))
    (F' := fun s (u : ℝ) =>
      ((u : ℂ) ^ (s - 1) * Complex.log (u : ℂ)) * cexp (-(u : ℂ) ^ 2 / 2 - z * u))
    (bound := fun u : ℝ =>
      2 / δ * (u ^ (δ / 2 - 1) * rexp (-u ^ 2 / 2 - z.re * u)) +
        u ^ (2 * s₀.re) * rexp (-u ^ 2 / 2 - z.re * u))
    hball (Eventually.of_forall fun _ => Measurable.aestronglyMeasurable (by fun_prop))
    (integrableOn_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi hs₀' z)
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_ (hb1.add hb2) ?_
  · exact h.2.differentiableAt.differentiableWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu s hs
    have hu' : 0 < u := hu
    have hdist : |s.re - s₀.re| < δ :=
      (abs_re_le_norm (s - s₀)).trans_lt (by simpa [dist_eq_norm] using hs)
    have hδs : δ ≤ s.re := by linarith [hδ_def, (abs_lt.mp hdist).1]
    have hsR : s.re ≤ 2 * s₀.re := by linarith [hδ_def, (abs_lt.mp hdist).2]
    rw [mul_right_comm, norm_mul, ← Complex.ofReal_log hu'.le, Complex.norm_real, Real.norm_eq_abs,
      norm_cpow_mul_cexp_neg_sq_div_two_sub_mul s z hu']
    calc u ^ (s.re - 1) * rexp (-u ^ 2 / 2 - z.re * u) * |Real.log u|
        = (|Real.log u| * u ^ (s.re - 1)) * rexp (-u ^ 2 / 2 - z.re * u) := by ring
      _ ≤ (2 / δ * u ^ (δ / 2 - 1) + u ^ (2 * s₀.re)) * rexp (-u ^ 2 / 2 - z.re * u) := by
          gcongr
          exact abs_log_mul_rpow_le hu' hδ hδs hsR
      _ = 2 / δ * (u ^ (δ / 2 - 1) * rexp (-u ^ 2 / 2 - z.re * u)) +
            u ^ (2 * s₀.re) * rexp (-u ^ 2 / 2 - z.re * u) := by ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu s _
    have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hu)
    have hd := (((hasDerivAt_id s).sub_const (1 : ℂ)).const_cpow (Or.inl hu_ne)).mul_const
      (cexp (-(u : ℂ) ^ 2 / 2 - z * u))
    simpa using hd

/-- Positive rescaling of the Gaussian–Laplace integral: for `0 < c` and all `s z : ℂ` (including
non-integrable `s`, where both sides vanish), substituting `u = c v` pulls out `(c : ℂ) ^ s`. -/
theorem integral_cpow_mul_cexp_neg_div_sq_div_two_sub_mul_Ioi {c : ℝ} (hc : 0 < c) (s z : ℂ) :
    (∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * cexp (-((u : ℂ) / c) ^ 2 / 2 - z * u)) =
      (c : ℂ) ^ s *
        ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (s - 1) * cexp (-(v : ℂ) ^ 2 / 2 - z * c * v) := by
  have hc_ne : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hcongr :
      (∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * cexp (-((u : ℂ) / c) ^ 2 / 2 - z * u)) =
        ∫ u in Ioi (0 : ℝ), (c : ℂ) ^ (s - 1) *
          (((c⁻¹ * u : ℝ) : ℂ) ^ (s - 1) *
            cexp (-((c⁻¹ * u : ℝ) : ℂ) ^ 2 / 2 - z * c * (c⁻¹ * u : ℝ))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    have hmul : (u : ℂ) = ((c * (c⁻¹ * u) : ℝ) : ℂ) := by
      congr 1; exact (mul_inv_cancel_left₀ hc.ne' u).symm
    have hpow : (u : ℂ) ^ (s - 1) = (c : ℂ) ^ (s - 1) * ((c⁻¹ * u : ℝ) : ℂ) ^ (s - 1) := by
      have h_nonneg : 0 ≤ c⁻¹ * u := mul_nonneg (inv_pos.mpr hc).le (le_of_lt ‹0 < u›)
      rw [hmul, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hc.le h_nonneg (s - 1)]
    have hexp : -((u : ℂ) / c) ^ 2 / 2 - z * u =
        -((c⁻¹ * u : ℝ) : ℂ) ^ 2 / 2 - z * c * (c⁻¹ * u : ℝ) := by
      push_cast; field_simp
    rw [hpow, hexp, mul_assoc]
  have hcpow : (c : ℂ) ^ (s - 1) * (c : ℂ) = (c : ℂ) ^ s := by
    rw [Complex.cpow_sub _ _ hc_ne, Complex.cpow_one, div_mul_cancel₀ _ hc_ne]
  rw [hcongr, integral_const_mul,
    integral_comp_mul_left_Ioi
      (fun v : ℝ => (v : ℂ) ^ (s - 1) * cexp (-(v : ℂ) ^ 2 / 2 - z * c * v)) 0 (inv_pos.mpr hc)]
  simp only [inv_inv, mul_zero, Complex.real_smul, ← mul_assoc, hcpow]

/-! ### Majorants, absolute summability, and shifted-tail holomorphy -/

/-- Nonnegative half-Gamma Gaussian–Laplace majorant kernel for the `m`-th Hermite–Laplace term. -/
private noncomputable def hermiteMajorant (σ b r : ℝ) (m : ℕ) (u : ℝ) : ℝ :=
  u ^ (σ - 1) * rexp (-u ^ 2 / 2 - b * u) * ((r * u / √2) ^ m / Real.Gamma ((m : ℝ) / 2 + 1))

/-- Nonnegativity of `hermiteMajorant σ b r m u` for `0 ≤ r` and `0 < u`. -/
private theorem hermiteMajorant_nonneg {σ b r : ℝ} (hr : 0 ≤ r) (m : ℕ) {u : ℝ} (hu : 0 < u) :
    0 ≤ hermiteMajorant σ b r m u := by
  unfold hermiteMajorant
  have : 0 < Real.Gamma ((m : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  have : 0 < u ^ (σ - 1) := Real.rpow_pos_of_pos hu _
  positivity

/-- Each single `hermiteMajorant σ b r m` is integrable on `(0, ∞)` whenever `0 < σ + m`. -/
private theorem integrableOn_hermiteMajorant {σ : ℝ} (b r : ℝ) {m : ℕ} (hσm : 0 < σ + m) :
    IntegrableOn (hermiteMajorant σ b r m) (Ioi 0) := by
  have h := (integrableOn_rpow_mul_rexp_neg_sq_div_two_sub_mul_Ioi (σ := σ + m) hσm b).const_mul
    ((r / √2) ^ m / Real.Gamma ((m : ℝ) / 2 + 1))
  refine IntegrableOn.congr_fun h (fun u hu => ?_) measurableSet_Ioi
  unfold hermiteMajorant
  rw [show σ + (m : ℝ) - 1 = (σ - 1) + (m : ℝ) by ring, Real.rpow_add hu, Real.rpow_natCast,
    show r * u / √2 = r / √2 * u by ring, mul_pow]
  ring

/-- Pointwise bound on the `m`-th Hermite–Laplace integrand for `u > 0`, derived from
`TauCeti.abs_aeval_hermite_mul_exp_div_factorial_le`. -/
private theorem norm_hermite_laplace_integrand_le (s z w : ℂ) (y : ℝ) (m : ℕ) {u : ℝ}
    (hu : 0 < u) :
    ‖w ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
        ((u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u))‖ ≤
      rexp (y ^ 2 / 2) * hermiteMajorant s.re z.re ‖w‖ m u := by
  have heval : aeval (y : ℂ) (hermite m) = ((aeval y (hermite m) : ℝ) : ℂ) :=
    Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℤ ℝ ℂ) y (hermite m)
  have h2pow : (2 : ℝ) ^ (-(m : ℝ) / 2) = ((√2)⁻¹) ^ m := by
    rw [inv_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul zero_le_two,
      ← Real.rpow_neg zero_le_two]
    congr 1; ring
  have hcoeff : |aeval y (hermite m)| / (m ! : ℝ) ≤
      rexp (y ^ 2 / 2) * (((√2)⁻¹) ^ m / Real.Gamma ((m : ℝ) / 2 + 1)) := by
    have hb := mul_le_mul_of_nonneg_left (abs_aeval_hermite_mul_exp_div_factorial_le m y)
      (Real.exp_pos (y ^ 2 / 2)).le
    have hexp_cancel : rexp (y ^ 2 / 2) *
        (|aeval y (hermite m)| * rexp (-(y ^ 2) / 2) / (m ! : ℝ)) =
        |aeval y (hermite m)| / (m ! : ℝ) := by
      calc rexp (y ^ 2 / 2) * (|aeval y (hermite m)| * rexp (-(y ^ 2) / 2) / (m ! : ℝ))
          = (rexp (y ^ 2 / 2) * rexp (-(y ^ 2) / 2)) * (|aeval y (hermite m)| / (m ! : ℝ)) := by
            ring
        _ = |aeval y (hermite m)| / (m ! : ℝ) := by
            rw [← Real.exp_add, show y ^ 2 / 2 + -(y ^ 2) / 2 = 0 by ring, Real.exp_zero, one_mul]
    rwa [hexp_cancel, h2pow] at hb
  rw [heval, norm_mul, norm_mul, norm_div, norm_pow, Complex.norm_natCast, Complex.norm_real,
    Real.norm_eq_abs, div_mul_eq_mul_div, mul_div_assoc,
    norm_cpow_mul_cexp_neg_sq_div_two_sub_mul (s + m) z hu]
  calc ‖w‖ ^ m * (|aeval y (hermite m)| / (m ! : ℝ)) *
          (u ^ ((s + m).re - 1) * rexp (-u ^ 2 / 2 - z.re * u))
      ≤ ‖w‖ ^ m * (rexp (y ^ 2 / 2) * (((√2)⁻¹) ^ m / Real.Gamma ((m : ℝ) / 2 + 1))) *
          (u ^ ((s + m).re - 1) * rexp (-u ^ 2 / 2 - z.re * u)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoeff (by positivity))
          (mul_nonneg (Real.rpow_pos_of_pos hu _).le (Real.exp_pos _).le)
    _ = rexp (y ^ 2 / 2) * hermiteMajorant s.re z.re ‖w‖ m u := by
        unfold hermiteMajorant
        have hexp_re : (s + m).re - 1 = (s.re - 1) + (m : ℝ) := by simp; ring
        rw [hexp_re, Real.rpow_add hu, Real.rpow_natCast, div_eq_mul_inv (‖w‖ * u) √2,
          mul_pow, mul_pow]
        ring

/-- Termwise Gaussian–half-Gamma majorant for the `m`-th Hermite-weighted Laplace integral, valid
for all `s z w : ℂ`, `y : ℝ`, and `m : ℕ` without restriction on `Re s`. -/
theorem norm_pow_div_factorial_mul_hermite_mul_integral_le (s z w : ℂ) (y : ℝ) (m : ℕ) :
    ‖w ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u)‖ ≤
      rexp (y ^ 2 / 2) *
        ∫ u in Ioi (0 : ℝ),
          u ^ (s.re - 1) * rexp (-u ^ 2 / 2 - z.re * u) *
            ((‖w‖ * u / √2) ^ m / Real.Gamma ((m : ℝ) / 2 + 1)) := by
  by_cases hsm : 0 < (s + m).re
  · rw [← integral_const_mul, ← integral_const_mul]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hint_lhs : IntegrableOn
        (fun u : ℝ => ‖w ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
          ((u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u))‖) (Ioi 0) :=
      ((integrableOn_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi hsm z).const_mul _).norm
    have hint_rhs : IntegrableOn
        (fun u : ℝ => rexp (y ^ 2 / 2) * hermiteMajorant s.re z.re ‖w‖ m u) (Ioi 0) :=
      (integrableOn_hermiteMajorant z.re ‖w‖ (by simpa using hsm)).const_mul _
    exact setIntegral_mono_on hint_lhs hint_rhs measurableSet_Ioi fun u hu =>
      norm_hermite_laplace_integrand_le s z w y m hu
  · have hzero : (∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u)) =
        0 := integral_undef (mt integrableOn_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi_iff.mp hsm)
    rw [hzero, mul_zero, norm_zero]
    refine mul_nonneg (Real.exp_pos _).le (setIntegral_nonneg measurableSet_Ioi fun u hu => ?_)
    exact hermiteMajorant_nonneg (norm_nonneg w) m hu

/-- Pointwise vanishing-order Gaussian bound on the `M`-shifted `hermiteMajorant` sum for `u > 0`
and `0 ≤ r`, obtained from `Real.tsum_pow_add_div_Gamma_div_two_add_one_le`. -/
private theorem tsum_hermiteMajorant_le_exp {σ b r : ℝ} (hr : 0 ≤ r) (M : ℕ) {u : ℝ} (hu : 0 < u) :
    (∑' k : ℕ, hermiteMajorant σ b r (k + M) u) ≤
      4 / √π * (r / √2) ^ M / (M / 2)! *
        (u ^ (σ + M - 1) * rexp (-((1 - r ^ 2) / 2) * u ^ 2 - b * u)) := by
  unfold hermiteMajorant
  rw [tsum_mul_left]
  have htail := Real.tsum_pow_add_div_Gamma_div_two_add_one_le (r * u / √2) M
  have habs : |r * u / √2| = r * u / √2 := abs_of_nonneg (by positivity)
  have hsq : (r * u / √2) ^ 2 = r ^ 2 / 2 * u ^ 2 := by
    rw [div_pow, Real.sq_sqrt zero_le_two]; ring
  rw [habs, hsq] at htail
  calc u ^ (σ - 1) * rexp (-u ^ 2 / 2 - b * u) *
          (∑' k : ℕ, (r * u / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1))
      ≤ u ^ (σ - 1) * rexp (-u ^ 2 / 2 - b * u) *
          (4 / √π * (r * u / √2) ^ M / (M / 2)! * rexp (r ^ 2 / 2 * u ^ 2)) :=
        mul_le_mul_of_nonneg_left htail
          (mul_nonneg (Real.rpow_pos_of_pos hu _).le (Real.exp_pos _).le)
    _ = 4 / √π * (r / √2) ^ M / (M / 2)! *
          ((u ^ (σ - 1) * u ^ M) * (rexp (-u ^ 2 / 2 - b * u) * rexp (r ^ 2 / 2 * u ^ 2))) := by
        rw [show r * u / √2 = r / √2 * u by ring, mul_pow]
        ring
    _ = 4 / √π * (r / √2) ^ M / (M / 2)! *
          (u ^ (σ + M - 1) * rexp (-((1 - r ^ 2) / 2) * u ^ 2 - b * u)) := by
        rw [← Real.rpow_natCast u M, ← Real.rpow_add hu, ← Real.exp_add]
        congr 2 <;> ring_nf

/-- Pointwise polynomial-free bound on the `M`-shifted `hermiteMajorant` sum when `0 ≤ r ≤ 1`,
cancelling `exp(-u² / 2)` via `Real.tsum_pow_add_div_Gamma_div_two_add_one_lt_two_mul_exp`. -/
private theorem tsum_hermiteMajorant_le_two_mul {σ b r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (M : ℕ)
    {u : ℝ} (hu : 0 < u) :
    (∑' k : ℕ, hermiteMajorant σ b r (k + M) u) ≤ 2 * u ^ (σ - 1) * rexp (-b * u) := by
  unfold hermiteMajorant
  rw [tsum_mul_left]
  have htail := (Real.tsum_pow_add_div_Gamma_div_two_add_one_lt_two_mul_exp (r * u / √2) M).le
  have hsq : (r * u / √2) ^ 2 ≤ u ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt zero_le_two]
    have hr_sq : r ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg u]
  have : 0 < u ^ (σ - 1) := Real.rpow_pos_of_pos hu _
  calc u ^ (σ - 1) * rexp (-u ^ 2 / 2 - b * u) *
          (∑' k : ℕ, (r * u / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1))
      ≤ u ^ (σ - 1) * rexp (-u ^ 2 / 2 - b * u) * (2 * rexp ((r * u / √2) ^ 2)) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
    _ ≤ u ^ (σ - 1) * rexp (-u ^ 2 / 2 - b * u) * (2 * rexp (u ^ 2 / 2)) := by gcongr
    _ = 2 * u ^ (σ - 1) * (rexp (-u ^ 2 / 2 - b * u) * rexp (u ^ 2 / 2)) := by ring
    _ = 2 * u ^ (σ - 1) * rexp (-b * u) := by
        rw [← Real.exp_add]; congr 2; ring

/-- For `0 < σ + M` and `0 ≤ r < 1`, the `M`-shifted `hermiteMajorant` sum is integrable on
`(0, ∞)` for every real linear rate `b`. -/
private theorem integrableOn_tsum_hermiteMajorant_of_lt_one {σ b r : ℝ} {M : ℕ}
    (hσM : 0 < σ + M) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    IntegrableOn (fun u : ℝ => ∑' k : ℕ, hermiteMajorant σ b r (k + M) u) (Ioi 0) := by
  have hq : 0 < (1 - r ^ 2) / 2 := by nlinarith
  have hdom : IntegrableOn
      (fun u : ℝ => 4 / √π * (r / √2) ^ M / (M / 2)! *
        (u ^ (σ + M - 1) * rexp (-((1 - r ^ 2) / 2) * u ^ 2 - b * u))) (Ioi 0) := by
    have hc := (integrableOn_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi
      (s := ((σ + M : ℝ) : ℂ)) (q := (((1 - r ^ 2) / 2 : ℝ) : ℂ))
      (by exact_mod_cast hσM) (by exact_mod_cast hq) (b : ℂ)).norm.const_mul
      (4 / √π * (r / √2) ^ M / (M / 2)!)
    refine IntegrableOn.congr_fun hc (fun u hu => ?_) measurableSet_Ioi
    have hn := norm_cpow_mul_cexp_neg_mul_sq_sub_mul ((σ + M : ℝ) : ℂ)
      (((1 - r ^ 2) / 2 : ℝ) : ℂ) (b : ℂ) hu
    rw [Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_re] at hn
    exact congrArg (4 / √π * (r / √2) ^ M / (M / 2)! * ·) hn
  refine hdom.mono' (AEStronglyMeasurable.tsum fun k =>
    Measurable.aestronglyMeasurable (by unfold hermiteMajorant; fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_of_nonneg (tsum_nonneg fun k => hermiteMajorant_nonneg hr0 (k + M) hu)]
  exact tsum_hermiteMajorant_le_exp hr0 M hu

/-- On `(0, 1]`, the `M`-shifted `hermiteMajorant` sum is integrable whenever `0 < σ + M` and
`0 ≤ r ≤ 1` (including the endpoint `r = 1`). -/
private theorem integrableOn_tsum_hermiteMajorant_Ioc {σ b r : ℝ} {M : ℕ}
    (hσM : 0 < σ + M) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    IntegrableOn (fun u : ℝ => ∑' k : ℕ, hermiteMajorant σ b r (k + M) u) (Ioc 0 1) := by
  have hrpow : IntegrableOn (fun u : ℝ => u ^ (σ + M - 1)) (Ioc 0 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
  set C := 4 / √π * (r / √2) ^ M / (M / 2)! * rexp |b|
  have hC : 0 ≤ 4 / √π * (r / √2) ^ M / (M / 2)! := by positivity
  refine (hrpow.const_mul C).mono' (AEStronglyMeasurable.tsum fun k =>
    Measurable.aestronglyMeasurable (by unfold hermiteMajorant; fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  have hu0 : 0 < u := hu.1
  rw [Real.norm_of_nonneg (tsum_nonneg fun k => hermiteMajorant_nonneg hr0 (k + M) hu0)]
  refine (tsum_hermiteMajorant_le_exp hr0 M hu0).trans ?_
  have hr_sq : 0 ≤ (1 - r ^ 2) / 2 * u ^ 2 := by
    have : r ^ 2 ≤ 1 := by nlinarith
    positivity
  have hbu : -b * u ≤ |b| := by
    have : (-b) * u ≤ |-b * u| := le_abs_self _
    rw [abs_mul, abs_neg, abs_of_pos hu0] at this
    nlinarith [hu.2, abs_nonneg b]
  have hexp : rexp (-((1 - r ^ 2) / 2) * u ^ 2 - b * u) ≤ rexp |b| :=
    Real.exp_le_exp.mpr (by linarith)
  calc 4 / √π * (r / √2) ^ M / (M / 2)! *
          (u ^ (σ + M - 1) * rexp (-((1 - r ^ 2) / 2) * u ^ 2 - b * u))
      ≤ 4 / √π * (r / √2) ^ M / (M / 2)! * (u ^ (σ + M - 1) * rexp |b|) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hexp (Real.rpow_pos_of_pos hu0 _).le) hC
    _ = C * u ^ (σ + M - 1) := by ring

/-- For `0 < σ + M`, `0 ≤ r ≤ 1`, and `0 < b`, the `M`-shifted `hermiteMajorant` sum is integrable
on `(0, ∞)`. -/
private theorem integrableOn_tsum_hermiteMajorant_of_pos {σ b r : ℝ} {M : ℕ}
    (hσM : 0 < σ + M) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => ∑' k : ℕ, hermiteMajorant σ b r (k + M) u) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine (integrableOn_tsum_hermiteMajorant_Ioc hσM hr0 hr1).union ?_
  set p := max σ 1
  have hp : 0 < p := lt_of_lt_of_le zero_lt_one (le_max_right σ 1)
  have htail : IntegrableOn (fun u : ℝ => 2 * (u ^ (p - 1) * rexp (-b * u))) (Ioi 1) := by
    have h0 := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := p - 1) (b := b)
      (by linarith) one_pos hb
    simp only [Real.rpow_one] at h0
    exact IntegrableOn.mono_set (h0.const_mul 2) (Ioi_subset_Ioi zero_le_one)
  refine htail.mono' (AEStronglyMeasurable.tsum fun k =>
    Measurable.aestronglyMeasurable (by unfold hermiteMajorant; fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := zero_lt_one.trans hu
  rw [Real.norm_of_nonneg (tsum_nonneg fun k => hermiteMajorant_nonneg hr0 (k + M) hu0)]
  refine (tsum_hermiteMajorant_le_two_mul hr0 hr1 M hu0).trans ?_
  have hrpow : u ^ (σ - 1) ≤ u ^ (p - 1) :=
    Real.rpow_le_rpow_of_exponent_le (le_of_lt hu) (by linarith [le_max_left σ 1])
  calc 2 * u ^ (σ - 1) * rexp (-b * u)
      ≤ 2 * u ^ (p - 1) * rexp (-b * u) := by gcongr
    _ = 2 * (u ^ (p - 1) * rexp (-b * u)) := by ring

/-- For `0 < σ + M`, `σ < 0`, `0 ≤ r ≤ 1`, and `0 ≤ b`, the `M`-shifted `hermiteMajorant` sum is
integrable on `(0, ∞)`. -/
private theorem integrableOn_tsum_hermiteMajorant_of_neg {σ b r : ℝ} {M : ℕ}
    (hσM : 0 < σ + M) (hσ : σ < 0) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hb : 0 ≤ b) :
    IntegrableOn (fun u : ℝ => ∑' k : ℕ, hermiteMajorant σ b r (k + M) u) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine (integrableOn_tsum_hermiteMajorant_Ioc hσM hr0 hr1).union ?_
  have htail : IntegrableOn (fun u : ℝ => 2 * u ^ (σ - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul 2
  refine htail.mono' (AEStronglyMeasurable.tsum fun k =>
    Measurable.aestronglyMeasurable (by unfold hermiteMajorant; fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := zero_lt_one.trans hu
  rw [Real.norm_of_nonneg (tsum_nonneg fun k => hermiteMajorant_nonneg hr0 (k + M) hu0)]
  refine (tsum_hermiteMajorant_le_two_mul hr0 hr1 M hu0).trans ?_
  have hexp : rexp (-b * u) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  calc 2 * u ^ (σ - 1) * rexp (-b * u)
      ≤ 2 * u ^ (σ - 1) * 1 :=
        mul_le_mul_of_nonneg_left hexp (mul_nonneg zero_le_two (Real.rpow_pos_of_pos hu0 _).le)
    _ = 2 * u ^ (σ - 1) := mul_one _

/-- Dominated convergence converts integrability of `∑' k, hermiteMajorant σ b r (k + M)` on
`(0, ∞)` into summability of the sequence of integrals. -/
private theorem summable_integral_hermiteMajorant {σ b r : ℝ} {M : ℕ} (hr0 : 0 ≤ r)
    (hint : IntegrableOn (fun u : ℝ => ∑' k : ℕ, hermiteMajorant σ b r (k + M) u) (Ioi 0)) :
    Summable fun k : ℕ => ∫ u in Ioi (0 : ℝ), hermiteMajorant σ b r (k + M) u := by
  have hsum : ∀ u : ℝ, Summable fun k : ℕ => hermiteMajorant σ b r (k + M) u := fun u => by
    unfold hermiteMajorant
    exact ((summable_nat_add_iff M).2
      (Real.summable_pow_div_Gamma_div_two_add_one (r * u / √2))).mul_left _
  exact (hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun k u => hermiteMajorant σ b r (k + M) u)
    (f := fun u => ∑' k : ℕ, hermiteMajorant σ b r (k + M) u)
    (bound := fun k u => hermiteMajorant σ b r (k + M) u)
    (fun k => Measurable.aestronglyMeasurable (by unfold hermiteMajorant; fun_prop))
    (fun k => by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [Real.norm_of_nonneg (hermiteMajorant_nonneg hr0 (k + M) hu)])
    (Eventually.of_forall fun u => hsum u)
    hint
    (Eventually.of_forall fun u => (hsum u).hasSum)).summable

/-- In the open unit disk `‖w‖ < 1`, the Hermite-weighted Laplace series is norm-summable for
every `s z : ℂ` and `y : ℝ` (with no restriction on `Re s` or `Re z`). -/
theorem summable_norm_pow_div_factorial_mul_hermite_mul_integral_of_norm_lt_one
    {w : ℂ} (hw : ‖w‖ < 1) (s z : ℂ) (y : ℝ) :
    Summable fun m : ℕ =>
      ‖w ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u)‖ := by
  obtain ⟨M, hM⟩ := exists_nat_gt (-s.re)
  rw [← summable_nat_add_iff M]
  have hmaj := (summable_integral_hermiteMajorant (norm_nonneg w)
    (integrableOn_tsum_hermiteMajorant_of_lt_one (σ := s.re) (b := z.re) (M := M)
      (by linarith) (norm_nonneg w) hw)).mul_left (rexp (y ^ 2 / 2))
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => norm_pow_div_factorial_mul_hermite_mul_integral_le s z w y (k + M)) hmaj

/-- On the closed unit disk `‖w‖ ≤ 1` (including `w = 1`, i.e. `t = π / 4`), the Hermite-weighted
Laplace series is norm-summable whenever `0 < Re z`, for every `s : ℂ` and `y : ℝ`. -/
theorem summable_norm_pow_div_factorial_mul_hermite_mul_integral_of_re_pos
    {z w : ℂ} (hw : ‖w‖ ≤ 1) (hz : 0 < z.re) (s : ℂ) (y : ℝ) :
    Summable fun m : ℕ =>
      ‖w ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u)‖ := by
  obtain ⟨M, hM⟩ := exists_nat_gt (-s.re)
  rw [← summable_nat_add_iff M]
  have hmaj := (summable_integral_hermiteMajorant (norm_nonneg w)
    (integrableOn_tsum_hermiteMajorant_of_pos (σ := s.re) (b := z.re) (M := M)
      (by linarith) (norm_nonneg w) hw hz)).mul_left (rexp (y ^ 2 / 2))
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => norm_pow_div_factorial_mul_hermite_mul_integral_le s z w y (k + M)) hmaj

/-- On the closed unit disk `‖w‖ ≤ 1`, when `0 ≤ Re z` and `Re s < 0` (covering the endpoint case
`x = 0`, `Re a < -1 / 2` in DLMF 12.13.5), the Hermite-weighted Laplace series is norm-summable for
every `y : ℝ`. -/
theorem summable_norm_pow_div_factorial_mul_hermite_mul_integral_of_re_neg
    {s z w : ℂ} (hw : ‖w‖ ≤ 1) (hz : 0 ≤ z.re) (hs : s.re < 0) (y : ℝ) :
    Summable fun m : ℕ =>
      ‖w ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u)‖ := by
  obtain ⟨M, hM⟩ := exists_nat_gt (-s.re)
  rw [← summable_nat_add_iff M]
  have hmaj := (summable_integral_hermiteMajorant (norm_nonneg w)
    (integrableOn_tsum_hermiteMajorant_of_neg (σ := s.re) (b := z.re) (M := M)
      (by linarith) hs (norm_nonneg w) hw hz)).mul_left (rexp (y ^ 2 / 2))
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => norm_pow_div_factorial_mul_hermite_mul_integral_le s z w y (k + M)) hmaj

/-- Uniform two-endpoint majorant for the `m`-th Hermite–Laplace term across a vertical strip
`σ₁ ≤ Re s ≤ σ₂` with `0 < σ₁ + m`. -/
private theorem norm_hermite_laplace_term_le_sum_majorant {σ₁ σ₂ : ℝ} {s : ℂ} (z w : ℂ) (y : ℝ)
    {m : ℕ} (hσ₁m : 0 < σ₁ + m) (hσ₁ : σ₁ ≤ s.re) (hσ₂ : s.re ≤ σ₂) :
    ‖w ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u)‖ ≤
      rexp (y ^ 2 / 2) *
        ((∫ u in Ioi (0 : ℝ), hermiteMajorant σ₁ z.re ‖w‖ m u) +
          ∫ u in Ioi (0 : ℝ), hermiteMajorant σ₂ z.re ‖w‖ m u) := by
  refine (norm_pow_div_factorial_mul_hermite_mul_integral_le s z w y m).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hint1 : IntegrableOn (hermiteMajorant σ₁ z.re ‖w‖ m) (Ioi 0) :=
    integrableOn_hermiteMajorant z.re ‖w‖ hσ₁m
  have hint2 : IntegrableOn (hermiteMajorant σ₂ z.re ‖w‖ m) (Ioi 0) :=
    integrableOn_hermiteMajorant z.re ‖w‖ (by linarith)
  have hints : IntegrableOn (hermiteMajorant s.re z.re ‖w‖ m) (Ioi 0) :=
    integrableOn_hermiteMajorant z.re ‖w‖ (by linarith)
  rw [← integral_add hint1 hint2]
  refine setIntegral_mono_on hints (hint1.add hint2) measurableSet_Ioi fun u hu => ?_
  have hu' : 0 < u := hu
  have hrpow : u ^ (s.re - 1) ≤ u ^ (σ₁ - 1) + u ^ (σ₂ - 1) := by
    rcases le_or_gt u 1 with hu1 | hu1
    · exact (Real.rpow_le_rpow_of_exponent_ge hu' hu1 (by linarith)).trans
        (le_add_of_nonneg_right (Real.rpow_pos_of_pos hu' _).le)
    · exact (Real.rpow_le_rpow_of_exponent_le hu1.le (by linarith)).trans
        (le_add_of_nonneg_left (Real.rpow_pos_of_pos hu' _).le)
  have : 0 < Real.Gamma ((m : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  dsimp [Pi.add_apply, hermiteMajorant]
  calc u ^ (s.re - 1) * rexp (-u ^ 2 / 2 - z.re * u) *
          ((‖w‖ * u / √2) ^ m / Real.Gamma ((m : ℝ) / 2 + 1))
      ≤ (u ^ (σ₁ - 1) + u ^ (σ₂ - 1)) * rexp (-u ^ 2 / 2 - z.re * u) *
          ((‖w‖ * u / √2) ^ m / Real.Gamma ((m : ℝ) / 2 + 1)) := by gcongr
    _ = u ^ (σ₁ - 1) * rexp (-u ^ 2 / 2 - z.re * u) *
          ((‖w‖ * u / √2) ^ m / Real.Gamma ((m : ℝ) / 2 + 1)) +
        u ^ (σ₂ - 1) * rexp (-u ^ 2 / 2 - z.re * u) *
          ((‖w‖ * u / √2) ^ m / Real.Gamma ((m : ℝ) / 2 + 1)) := by ring

/-- Local Weierstrass M-test for the `M`-shifted Hermite–Laplace tail on `{s : ℂ | 0 < Re s + M}`
given summability of the majorant integrals at every parameter `σ` with `0 < σ + M`. -/
private theorem differentiableOn_tsum_add_of_summable_majorant (z w : ℂ) (y : ℝ) (M : ℕ)
    (hmaj_sum : ∀ σ : ℝ, 0 < σ + M →
      Summable fun k : ℕ => ∫ u in Ioi (0 : ℝ), hermiteMajorant σ z.re ‖w‖ (k + M) u) :
    DifferentiableOn ℂ
      (fun s : ℂ => ∑' k : ℕ,
        w ^ (k + M) / ((k + M)! : ℂ) * aeval (y : ℂ) (hermite (k + M)) *
          ∫ u in Ioi (0 : ℝ),
            (u : ℂ) ^ (s + (k + M : ℕ) - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u))
      {s : ℂ | 0 < s.re + M} := by
  intro s₀ hs₀
  have hs₀' : 0 < s₀.re + M := hs₀
  set δ := (s₀.re + M) / 2 with hδ_def
  have hδ : 0 < δ := by positivity
  set B := Metric.ball s₀ δ
  set σ₁ := δ - M
  set σ₂ := s₀.re + δ
  have hu_sum : Summable fun k : ℕ => rexp (y ^ 2 / 2) *
      ((∫ u in Ioi (0 : ℝ), hermiteMajorant σ₁ z.re ‖w‖ (k + M) u) +
        ∫ u in Ioi (0 : ℝ), hermiteMajorant σ₂ z.re ‖w‖ (k + M) u) :=
    ((hmaj_sum σ₁ (by dsimp [σ₁]; linarith)).add
      (hmaj_sum σ₂ (by dsimp [σ₂]; linarith))).mul_left _
  have hdiff_term (k : ℕ) : DifferentiableOn ℂ
      (fun s : ℂ => w ^ (k + M) / ((k + M)! : ℂ) * aeval (y : ℂ) (hermite (k + M)) *
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + (k + M : ℕ) - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u))
      B := by
    refine DifferentiableOn.const_mul ?_ _
    refine (differentiableOn_integral_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi z).comp
      (differentiable_id.add (differentiable_const ((k + M : ℕ) : ℂ))).differentiableOn
      fun s hs => ?_
    have hdist : |s.re - s₀.re| < δ :=
      (abs_re_le_norm (s - s₀)).trans_lt (by simpa [B, dist_eq_norm] using hs)
    change 0 < (s + (k + M : ℕ)).re
    rw [Complex.add_re, Complex.natCast_re, Nat.cast_add]
    linarith [hδ_def, (abs_lt.mp hdist).1, Nat.cast_nonneg (α := ℝ) k]
  have hbound (k : ℕ) (s : ℂ) (hs : s ∈ B) :
      ‖w ^ (k + M) / ((k + M)! : ℂ) * aeval (y : ℂ) (hermite (k + M)) *
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + (k + M : ℕ) - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u)‖ ≤
      rexp (y ^ 2 / 2) *
        ((∫ u in Ioi (0 : ℝ), hermiteMajorant σ₁ z.re ‖w‖ (k + M) u) +
          ∫ u in Ioi (0 : ℝ), hermiteMajorant σ₂ z.re ‖w‖ (k + M) u) := by
    have hdist : |s.re - s₀.re| < δ :=
      (abs_re_le_norm (s - s₀)).trans_lt (by simpa [B, dist_eq_norm] using hs)
    exact norm_hermite_laplace_term_le_sum_majorant z w y
      (by dsimp [σ₁]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) k])
      (by dsimp [σ₁]; linarith [hδ_def, (abs_lt.mp hdist).1])
      (by dsimp [σ₂]; linarith [(abs_lt.mp hdist).2])
  exact ((Complex.differentiableOn_tsum_of_summable_norm hu_sum hdiff_term Metric.isOpen_ball
    hbound).differentiableAt (Metric.ball_mem_nhds s₀ hδ)).differentiableWithinAt

/-- For `‖w‖ < 1` and every `M : ℕ`, `z : ℂ`, and `y : ℝ`, the `M`-shifted Hermite–Laplace tail is
holomorphic in `s` on the half-plane `{s : ℂ | 0 < Re s + M}`. -/
theorem differentiableOn_tsum_pow_div_factorial_mul_hermite_mul_integral_add_of_norm_lt_one
    {w : ℂ} (hw : ‖w‖ < 1) (z : ℂ) (y : ℝ) (M : ℕ) :
    DifferentiableOn ℂ
      (fun s : ℂ => ∑' k : ℕ,
        w ^ (k + M) / ((k + M)! : ℂ) * aeval (y : ℂ) (hermite (k + M)) *
          ∫ u in Ioi (0 : ℝ),
            (u : ℂ) ^ (s + (k + M : ℕ) - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u))
      {s : ℂ | 0 < s.re + M} :=
  differentiableOn_tsum_add_of_summable_majorant z w y M fun _ hσM =>
    summable_integral_hermiteMajorant (norm_nonneg w)
      (integrableOn_tsum_hermiteMajorant_of_lt_one hσM (norm_nonneg w) hw)

/-- At the unit-circle endpoint `w = 1` (covering both `t = -π / 4` directly and `t = π / 4` via
`y ↦ -y` and `Polynomial.hermite_parity`), when `0 < Re z`, the `M`-shifted Hermite–Laplace tail is
holomorphic in `s` on `{s : ℂ | 0 < Re s + M}` for every `M : ℕ` and `y : ℝ`. -/
theorem differentiableOn_tsum_div_factorial_mul_hermite_mul_integral_add_of_re_pos
    {z : ℂ} (hz : 0 < z.re) (y : ℝ) (M : ℕ) :
    DifferentiableOn ℂ
      (fun s : ℂ => ∑' k : ℕ,
        aeval (y : ℂ) (hermite (k + M)) / ((k + M)! : ℂ) *
          ∫ u in Ioi (0 : ℝ),
            (u : ℂ) ^ (s + (k + M : ℕ) - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u))
      {s : ℂ | 0 < s.re + M} := by
  have h := differentiableOn_tsum_add_of_summable_majorant z 1 y M fun _ hσM =>
    summable_integral_hermiteMajorant (norm_nonneg (1 : ℂ))
      (integrableOn_tsum_hermiteMajorant_of_pos hσM (norm_nonneg (1 : ℂ)) (by simp) hz)
  exact h.congr fun _ _ => tsum_congr fun _ => by ring

/-! ### Generating series, rotational addition, and endpoint Abel limit -/

/-- Pointwise Hermite generating series identity for the Gaussian–Laplace integrand at `u > 0`. -/
private theorem hasSum_hermite_laplace_integrand (s z w : ℂ) (y : ℝ) {u : ℝ} (hu : 0 < u) :
    HasSum
      (fun m : ℕ => (-w) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
        ((u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u)))
      ((u : ℂ) ^ (s - 1) * cexp (-(1 + w ^ 2) * (u : ℂ) ^ 2 / 2 - (z + w * y) * u)) := by
  have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hgen := (Polynomial.hasSum_hermite_generating_function (y : ℂ) (-w * u)).mul_right
    ((u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u))
  have hsum_eq : cexp ((y : ℂ) * (-w * u) - (-w * u) ^ 2 / 2) *
      ((u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u)) =
      (u : ℂ) ^ (s - 1) * cexp (-(1 + w ^ 2) * (u : ℂ) ^ 2 / 2 - (z + w * y) * u) := by
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2; ring
  rw [hsum_eq] at hgen
  refine hgen.congr_fun fun m => ?_
  have hpow : (u : ℂ) ^ (s + m - 1) = (u : ℂ) ^ (s - 1) * (u : ℂ) ^ m := by
    rw [show s + (m : ℂ) - 1 = (s - 1) + (m : ℂ) by ring, Complex.cpow_add _ _ hu_ne,
      Complex.cpow_natCast]
  rw [hpow, mul_pow]
  ring

/-- Dominated-convergence interchange of the Hermite generating series and the Gaussian–Laplace
integral on `(0, ∞)` whenever the `M = 0` majorant sum is integrable. -/
private theorem hasSum_of_integrableOn_tsum_majorant (s z w : ℂ) (y : ℝ)
    (hint : IntegrableOn (fun u : ℝ => ∑' m : ℕ, hermiteMajorant s.re z.re ‖w‖ m u) (Ioi 0)) :
    HasSum
      (fun m : ℕ => (-w) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u))
      (∫ u in Ioi (0 : ℝ),
        (u : ℂ) ^ (s - 1) * cexp (-(1 + w ^ 2) * (u : ℂ) ^ 2 / 2 - (z + w * y) * u)) := by
  have hdom : IntegrableOn
      (fun u : ℝ => ∑' m : ℕ, rexp (y ^ 2 / 2) * hermiteMajorant s.re z.re ‖w‖ m u) (Ioi 0) :=
    IntegrableOn.congr_fun (hint.const_mul (rexp (y ^ 2 / 2)))
      (fun u _ => tsum_mul_left.symm) measurableSet_Ioi
  have hsum_maj : ∀ u : ℝ,
      Summable fun m : ℕ => rexp (y ^ 2 / 2) * hermiteMajorant s.re z.re ‖w‖ m u := fun u => by
    unfold hermiteMajorant
    exact ((Real.summable_pow_div_Gamma_div_two_add_one (‖w‖ * u / √2)).mul_left _).mul_left _
  have hdct := hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun m (u : ℝ) => (-w) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
      ((u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u)))
    (f := fun u : ℝ =>
      (u : ℂ) ^ (s - 1) * cexp (-(1 + w ^ 2) * (u : ℂ) ^ 2 / 2 - (z + w * y) * u))
    (bound := fun m u => rexp (y ^ 2 / 2) * hermiteMajorant s.re z.re ‖w‖ m u)
    (fun m => Measurable.aestronglyMeasurable (by fun_prop))
    (fun m => by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      simpa [norm_neg] using norm_hermite_laplace_integrand_le s z (-w) y m hu)
    (Eventually.of_forall hsum_maj)
    hdom
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact hasSum_hermite_laplace_integrand s z w y hu)
  exact hdct.congr_fun fun m => (integral_const_mul _ _).symm

/-- For `0 < Re s` and `‖w‖ < 1`, the Hermite-weighted Laplace series sums to the deformed
Gaussian–Laplace integral `∫₀^∞ u^{s - 1} exp(-(1 + w²) u² / 2 - (z + w y) u) du` for every `z : ℂ`
and `y : ℝ`. -/
theorem hasSum_pow_div_factorial_mul_hermite_mul_integral_of_norm_lt_one
    {s w : ℂ} (hs : 0 < s.re) (hw : ‖w‖ < 1) (z : ℂ) (y : ℝ) :
    HasSum
      (fun m : ℕ => (-w) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u))
      (∫ u in Ioi (0 : ℝ),
        (u : ℂ) ^ (s - 1) * cexp (-(1 + w ^ 2) * (u : ℂ) ^ 2 / 2 - (z + w * y) * u)) :=
  hasSum_of_integrableOn_tsum_majorant s z w y <| by
    simpa using integrableOn_tsum_hermiteMajorant_of_lt_one (σ := s.re) (b := z.re) (M := 0)
      (by simpa using hs) (norm_nonneg w) hw

/-- On the closed unit disk `‖w‖ ≤ 1` (including the endpoint `w = 1`), for `0 < Re s` and
`0 < Re z`, the Hermite-weighted Laplace series sums to
`∫₀^∞ u^{s - 1} exp(-(1 + w²) u² / 2 - (z + w y) u) du` for every `y : ℝ`. -/
theorem hasSum_pow_div_factorial_mul_hermite_mul_integral_of_re_pos
    {s z w : ℂ} (hs : 0 < s.re) (hz : 0 < z.re) (hw : ‖w‖ ≤ 1) (y : ℝ) :
    HasSum
      (fun m : ℕ => (-w) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u))
      (∫ u in Ioi (0 : ℝ),
        (u : ℂ) ^ (s - 1) * cexp (-(1 + w ^ 2) * (u : ℂ) ^ 2 / 2 - (z + w * y) * u)) :=
  hasSum_of_integrableOn_tsum_majorant s z w y <| by
    simpa using integrableOn_tsum_hermiteMajorant_of_pos (σ := s.re) (b := z.re) (M := 0)
      (by simpa using hs) (norm_nonneg w) hw hz

/-- Trigonometric evaluation of the deformed Gaussian–Laplace integral at `w = tan t` whenever
`0 < cos t`. -/
private theorem integral_tan_laplace_eq {t : ℝ} (hc : 0 < Real.cos t) (s z : ℂ) (y : ℝ) :
    (Real.cos t : ℂ) ^ (-s) *
        (∫ u in Ioi (0 : ℝ),
          (u : ℂ) ^ (s - 1) *
            cexp (-(1 + (Real.tan t : ℂ) ^ 2) * (u : ℂ) ^ 2 / 2 -
              (z + (Real.tan t : ℂ) * y) * u)) =
      ∫ v in Ioi (0 : ℝ),
        (v : ℂ) ^ (s - 1) * cexp (-(v : ℂ) ^ 2 / 2 - (z * Real.cos t + y * Real.sin t) * v) := by
  have hc_ne : (Real.cos t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have h1tan : 1 + (Real.tan t : ℂ) ^ 2 = ((Real.cos t : ℂ) ^ 2)⁻¹ := by
    have hsc : (Real.sin t : ℂ) ^ 2 + (Real.cos t : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.sin_sq_add_cos_sq t
    rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div]
    field_simp
    linear_combination hsc
  have hlin : (z + (Real.tan t : ℂ) * y) * (Real.cos t : ℂ) =
      z * Real.cos t + y * Real.sin t := by
    rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div]
    field_simp
  have hint_eq :
      (∫ u in Ioi (0 : ℝ),
        (u : ℂ) ^ (s - 1) *
          cexp (-(1 + (Real.tan t : ℂ) ^ 2) * (u : ℂ) ^ 2 / 2 -
            (z + (Real.tan t : ℂ) * y) * u)) =
      ∫ u in Ioi (0 : ℝ),
        (u : ℂ) ^ (s - 1) *
          cexp (-((u : ℂ) / Real.cos t) ^ 2 / 2 - (z + (Real.tan t : ℂ) * y) * u) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [h1tan, div_pow]
    ring_nf
  rw [hint_eq,
    integral_cpow_mul_cexp_neg_div_sq_div_two_sub_mul_Ioi hc s (z + (Real.tan t : ℂ) * y),
    hlin, ← mul_assoc, ← Complex.cpow_add _ _ hc_ne, neg_add_cancel, Complex.cpow_zero, one_mul]

/-- Bound `|tan t| < 1` and `0 < cos t` for `|t| < π / 4`. -/
private theorem cos_pos_and_abs_tan_lt_one {t : ℝ} (ht : |t| < Real.pi / 4) :
    0 < Real.cos t ∧ |Real.tan t| < 1 := by
  have ht_lt : -(Real.pi / 2) < t ∧ t < Real.pi / 2 :=
    ⟨by linarith [(abs_lt.mp ht).1, Real.pi_pos], by linarith [(abs_lt.mp ht).2, Real.pi_pos]⟩
  refine ⟨Real.cos_pos_of_mem_Ioo ht_lt, abs_lt.mpr ⟨?_, ?_⟩⟩
  · have hmono := Real.strictMonoOn_tan
      (show -(Real.pi / 4) ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) by
        exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
      ht_lt (abs_lt.mp ht).1
    rwa [Real.tan_neg, Real.tan_pi_div_four] at hmono
  · have hmono := Real.strictMonoOn_tan ht_lt
      (show Real.pi / 4 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) by
        exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
      (abs_lt.mp ht).2
    rwa [Real.tan_pi_div_four] at hmono

/-- Bound `|tan t| ≤ 1` and `0 < cos t` on the closed interval `|t| ≤ π / 4`. -/
private theorem cos_pos_and_abs_tan_le_one {t : ℝ} (ht : |t| ≤ Real.pi / 4) :
    0 < Real.cos t ∧ |Real.tan t| ≤ 1 := by
  rcases lt_or_eq_of_le ht with hlt | heq
  · exact ⟨(cos_pos_and_abs_tan_lt_one hlt).1, (cos_pos_and_abs_tan_lt_one hlt).2.le⟩
  · rcases (abs_eq (by positivity)).mp heq with rfl | rfl <;>
      simp [Real.cos_pi_div_four, Real.tan_pi_div_four]

/-- Trigonometric Laplace–Hermite generating series for `0 < Re s` and `|t| < π / 4`:
`∑_{m ≥ 0} (cos t)^{-s} (-tan t)^m / m! * He_m(y) * I(s + m, z) = I(s, z cos t + y sin t)`. -/
theorem hasSum_tan_pow_div_factorial_mul_hermite_mul_integral
    {s : ℂ} {t : ℝ} (hs : 0 < s.re) (ht : |t| < Real.pi / 4) (z : ℂ) (y : ℝ) :
    HasSum
      (fun m : ℕ =>
        (Real.cos t : ℂ) ^ (-s) * ((-Real.tan t : ℂ) ^ m / (m ! : ℂ)) *
          aeval (y : ℂ) (hermite m) *
          ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u))
      (∫ u in Ioi (0 : ℝ),
        (u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - (z * Real.cos t + y * Real.sin t) * u)) := by
  obtain ⟨hc, htan⟩ := cos_pos_and_abs_tan_lt_one ht
  have hw : ‖(Real.tan t : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have h := (hasSum_pow_div_factorial_mul_hermite_mul_integral_of_norm_lt_one hs hw z y).mul_left
    ((Real.cos t : ℂ) ^ (-s))
  rw [integral_tan_laplace_eq hc s z y] at h
  exact h.congr_fun fun m => by ring

/-- Closed-interval trigonometric Laplace–Hermite generating series for `0 < Re s`, `0 < Re z`, and
`|t| ≤ π / 4` (including the endpoints `t = ±π / 4`). -/
theorem hasSum_tan_pow_div_factorial_mul_hermite_mul_integral_of_re_pos
    {s z : ℂ} {t : ℝ} (hs : 0 < s.re) (hz : 0 < z.re) (ht : |t| ≤ Real.pi / 4) (y : ℝ) :
    HasSum
      (fun m : ℕ =>
        (Real.cos t : ℂ) ^ (-s) * ((-Real.tan t : ℂ) ^ m / (m ! : ℂ)) *
          aeval (y : ℂ) (hermite m) *
          ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u))
      (∫ u in Ioi (0 : ℝ),
        (u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - (z * Real.cos t + y * Real.sin t) * u)) := by
  obtain ⟨hc, htan⟩ := cos_pos_and_abs_tan_le_one ht
  have hw : ‖(Real.tan t : ℂ)‖ ≤ 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have h := (hasSum_pow_div_factorial_mul_hermite_mul_integral_of_re_pos hs hz hw y).mul_left
    ((Real.cos t : ℂ) ^ (-s))
  rw [integral_tan_laplace_eq hc s z y] at h
  exact h.congr_fun fun m => by ring

/-- Algebraic rearrangement of the `m`-th summand into the DLMF 12.13.5 normalized rotational
addition form, using `(s)_m / Γ(s + m) = (Γ s)⁻¹` and `sin² t + cos² t = 1`. -/
private theorem rotational_addition_summand_eq (s z : ℂ) (y t : ℝ) (m : ℕ) :
    (cexp (-(z * Real.cos t + y * Real.sin t) ^ 2 / 4) * (Complex.Gamma s)⁻¹) *
        ((Real.cos t : ℂ) ^ (-s) * ((-Real.tan t : ℂ) ^ m / (m ! : ℂ)) *
          aeval (y : ℂ) (hermite m) *
          ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u)) =
      (Real.cos t : ℂ) ^ (-s) * cexp ((z * Real.sin t - y * Real.cos t) ^ 2 / 4) *
        ((-1 : ℂ) ^ m * (ascPochhammer ℂ m).eval s / (m ! : ℂ) * (Real.tan t : ℂ) ^ m) *
        (cexp (-z ^ 2 / 4) * (Complex.Gamma (s + m))⁻¹ *
          ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u)) *
        (cexp (-(y : ℂ) ^ 2 / 4) * aeval (y : ℂ) (hermite m)) := by
  have hG := (Complex.ascPochhammer_eval_div_Gamma_add_natCast s m).symm
  rw [div_eq_mul_inv] at hG
  have hsc : (Real.sin t : ℂ) ^ 2 + (Real.cos t : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq t
  have hexp : cexp (-(z * Real.cos t + y * Real.sin t) ^ 2 / 4) =
      cexp ((z * Real.sin t - y * Real.cos t) ^ 2 / 4) * cexp (-z ^ 2 / 4) *
        cexp (-(y : ℂ) ^ 2 / 4) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    linear_combination (-z ^ 2 / 4 - (y : ℂ) ^ 2 / 4) * hsc
  have htan_pow : (-(Real.tan t : ℂ)) ^ m = (-1 : ℂ) ^ m * (Real.tan t : ℂ) ^ m := by
    rw [neg_eq_neg_one_mul, mul_pow]
  rw [hG, hexp, htan_pow]
  ring

/-- **Rotational addition series in Laplace–Hermite form (DLMF 12.13.5, interior angles
`|t| < π / 4`).** For `0 < Re s`, `|t| < π / 4`, `z : ℂ`, and `y : ℝ`, with `s = a + 1 / 2` so that
each normalized Laplace integral equals `U(a + m, z)` (DLMF 12.5.1) and `exp(-y² / 4) He_m(y)`
equals `U(-m - 1 / 2, y)` (DLMF 12.7.2). -/
theorem hasSum_rotational_addition_laplaceHermite
    {s : ℂ} {t : ℝ} (hs : 0 < s.re) (ht : |t| < Real.pi / 4) (z : ℂ) (y : ℝ) :
    HasSum
      (fun m : ℕ =>
        (Real.cos t : ℂ) ^ (-s) * cexp ((z * Real.sin t - y * Real.cos t) ^ 2 / 4) *
          ((-1 : ℂ) ^ m * (ascPochhammer ℂ m).eval s / (m ! : ℂ) * (Real.tan t : ℂ) ^ m) *
          (cexp (-z ^ 2 / 4) * (Complex.Gamma (s + m))⁻¹ *
            ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u)) *
          (cexp (-(y : ℂ) ^ 2 / 4) * aeval (y : ℂ) (hermite m)))
      (cexp (-(z * Real.cos t + y * Real.sin t) ^ 2 / 4) * (Complex.Gamma s)⁻¹ *
        ∫ u in Ioi (0 : ℝ),
          (u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - (z * Real.cos t + y * Real.sin t) * u)) := by
  have h := (hasSum_tan_pow_div_factorial_mul_hermite_mul_integral hs ht z y).mul_left
    (cexp (-(z * Real.cos t + y * Real.sin t) ^ 2 / 4) * (Complex.Gamma s)⁻¹)
  exact h.congr_fun fun m => (rotational_addition_summand_eq s z y t m).symm

/-- **Rotational addition series on the closed interval `|t| ≤ π / 4` when `0 < Re z`
(DLMF 12.13.5, including the endpoint `t = π / 4`).** -/
theorem hasSum_rotational_addition_laplaceHermite_of_re_pos
    {s z : ℂ} {t : ℝ} (hs : 0 < s.re) (hz : 0 < z.re) (ht : |t| ≤ Real.pi / 4) (y : ℝ) :
    HasSum
      (fun m : ℕ =>
        (Real.cos t : ℂ) ^ (-s) * cexp ((z * Real.sin t - y * Real.cos t) ^ 2 / 4) *
          ((-1 : ℂ) ^ m * (ascPochhammer ℂ m).eval s / (m ! : ℂ) * (Real.tan t : ℂ) ^ m) *
          (cexp (-z ^ 2 / 4) * (Complex.Gamma (s + m))⁻¹ *
            ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u)) *
          (cexp (-(y : ℂ) ^ 2 / 4) * aeval (y : ℂ) (hermite m)))
      (cexp (-(z * Real.cos t + y * Real.sin t) ^ 2 / 4) * (Complex.Gamma s)⁻¹ *
        ∫ u in Ioi (0 : ℝ),
          (u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - (z * Real.cos t + y * Real.sin t) * u)) := by
  have h := (hasSum_tan_pow_div_factorial_mul_hermite_mul_integral_of_re_pos hs hz ht y).mul_left
    (cexp (-(z * Real.cos t + y * Real.sin t) ^ 2 / 4) * (Complex.Gamma s)⁻¹)
  exact h.congr_fun fun m => (rotational_addition_summand_eq s z y t m).symm

/-- **Endpoint Abel limit of the Laplace–Hermite generating series as `r → 1⁻`.** For `0 < Re s`
and *every* `z : ℂ` and `y : ℝ` (including `Re z ≤ 0`, where the `r = 1` series need not converge),
setting `t = arctan r` in `hasSum_tan_pow_div_factorial_mul_hermite_mul_integral` shows that the
`r`-weighted series converges as `r → 1⁻` to `(1 / √2)^s * I(s, (z + y) / √2)`. -/
theorem tendsto_abel_laplaceHermite {s : ℂ} (hs : 0 < s.re) (z : ℂ) (y : ℝ) :
    Tendsto
      (fun r : ℝ => ∑' m : ℕ, ((-r : ℝ) : ℂ) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u))
      (𝓝[<] 1)
      (𝓝 (((1 / √2 : ℝ) : ℂ) ^ s *
        ∫ u in Ioi (0 : ℝ),
          (u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - ((z + y) / √2) * u))) := by
  let g : ℝ → ℂ := fun r =>
    ((Real.cos (Real.arctan r) : ℝ) : ℂ) ^ s *
      ∫ u in Ioi (0 : ℝ),
        (u : ℂ) ^ (s - 1) *
          cexp (-(u : ℂ) ^ 2 / 2 -
            (z * Real.cos (Real.arctan r) + y * Real.sin (Real.arctan r)) * u)
  have hg_cont : ContinuousAt g 1 := by
    have hc1 : ContinuousAt (fun r : ℝ => ((Real.cos (Real.arctan r) : ℝ) : ℂ) ^ s) 1 :=
      ContinuousAt.comp (g := fun x : ℝ => (x : ℂ) ^ s)
        (f := fun r : ℝ => Real.cos (Real.arctan r))
        (Complex.continuousAt_ofReal_cpow_const _ s (Or.inr (Real.cos_arctan_pos 1).ne'))
        (Real.continuous_cos.comp Real.continuous_arctan).continuousAt
    have hc2 : ContinuousAt
        (fun r : ℝ => ∫ u in Ioi (0 : ℝ),
          (u : ℂ) ^ (s - 1) *
            cexp (-(u : ℂ) ^ 2 / 2 -
              (z * Real.cos (Real.arctan r) + y * Real.sin (Real.arctan r)) * u)) 1 :=
      ((differentiable_integral_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi s).continuous.comp
        (by fun_prop)).continuousAt
    exact hc1.mul hc2
  have hg1 : g 1 = ((1 / √2 : ℝ) : ℂ) ^ s *
      ∫ u in Ioi (0 : ℝ),
        (u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - ((z + y) / √2) * u) := by
    dsimp [g]
    rw [Real.cos_arctan, Real.sin_arctan]
    norm_num
    congr 2
    ext u
    simp [div_eq_mul_inv, add_mul]
  rw [← hg1]
  refine (hg_cont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1)] with r hr
  have ht : |Real.arctan r| < Real.pi / 4 := by
    rw [abs_lt]
    exact ⟨by rw [← Real.arctan_one, ← Real.arctan_neg]; exact Real.arctan_strictMono hr.1,
      by rw [← Real.arctan_one]; exact Real.arctan_strictMono hr.2⟩
  have hc_ne : ((Real.cos (Real.arctan r) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.cos_arctan_pos r).ne'
  have hsum := (hasSum_tan_pow_div_factorial_mul_hermite_mul_integral hs ht z y).mul_left
    (((Real.cos (Real.arctan r) : ℝ) : ℂ) ^ s)
  refine (hsum.congr_fun fun m => ?_).tsum_eq.symm
  rw [Real.tan_arctan, Complex.ofReal_neg]
  have hcancel : ((Real.cos (Real.arctan r) : ℝ) : ℂ) ^ s *
      ((Real.cos (Real.arctan r) : ℝ) ^ (-s)) = 1 := by
    rw [← Complex.cpow_add _ _ hc_ne, add_neg_cancel, Complex.cpow_zero]
  linear_combination (-(r : ℂ)) ^ m / (m ! : ℂ) * aeval (y : ℂ) (hermite m) *
    (∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u)) * hcancel.symm

/-- **Endpoint Abel limit of the DLMF 12.13.5 normalized rotational addition series at `t = π / 4`
as `r → 1⁻`.** Multiplying the `t = π / 4` summand by `r^m` and summing over `m ≥ 0` converges as
`r → 1⁻` to the normalized Laplace representation of `U(a, (z + y) / √2)` for `0 < Re s` and *all*
`z : ℂ`, `y : ℝ`. -/
theorem tendsto_abel_rotational_addition_laplaceHermite {s : ℂ} (hs : 0 < s.re) (z : ℂ) (y : ℝ) :
    Tendsto
      (fun r : ℝ => ∑' m : ℕ, (r : ℂ) ^ m *
        ((Real.cos (Real.pi / 4) : ℂ) ^ (-s) *
          cexp ((z * Real.sin (Real.pi / 4) - y * Real.cos (Real.pi / 4)) ^ 2 / 4) *
          ((-1 : ℂ) ^ m * (ascPochhammer ℂ m).eval s / (m ! : ℂ)) *
          (cexp (-z ^ 2 / 4) * (Complex.Gamma (s + m))⁻¹ *
            ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s + m - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u)) *
          (cexp (-(y : ℂ) ^ 2 / 4) * aeval (y : ℂ) (hermite m))))
      (𝓝[<] 1)
      (𝓝 (cexp (-((z + y) / √2) ^ 2 / 4) * (Complex.Gamma s)⁻¹ *
        ∫ u in Ioi (0 : ℝ),
          (u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - ((z + y) / √2) * u))) := by
  have hcos_eq : Real.cos (Real.pi / 4) = 1 / √2 := by
    rw [Real.cos_pi_div_four, div_eq_div_iff two_ne_zero (by positivity), one_mul,
      Real.mul_self_sqrt zero_le_two]
  have hsin_eq : Real.sin (Real.pi / 4) = 1 / √2 := by
    rw [Real.sin_pi_div_four, ← Real.cos_pi_div_four, hcos_eq]
  have hc_ne : ((1 / √2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  set P : ℂ := ((1 / √2 : ℝ) : ℂ) ^ (-s) * cexp (-((z + y) / √2) ^ 2 / 4) * (Complex.Gamma s)⁻¹
  set Ival : ℂ :=
    ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - ((z + y) / √2) * u)
  have hlim := (tendsto_abel_laplaceHermite hs z y).const_mul P
  have hlim_val : P * (((1 / √2 : ℝ) : ℂ) ^ s * Ival) =
      cexp (-((z + y) / √2) ^ 2 / 4) * (Complex.Gamma s)⁻¹ * Ival := by
    dsimp [P]
    have hcancel : ((1 / √2 : ℝ) : ℂ) ^ (-s) * ((1 / √2 : ℝ) : ℂ) ^ s = 1 := by
      rw [← Complex.cpow_add _ _ hc_ne, neg_add_cancel, Complex.cpow_zero]
    linear_combination cexp (-((z + y) / √2) ^ 2 / 4) * (Complex.Gamma s)⁻¹ * Ival * hcancel
  rw [hlim_val] at hlim
  refine hlim.congr fun r => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  have hlin : z * (Real.cos (Real.pi / 4) : ℂ) + (y : ℂ) * (Real.sin (Real.pi / 4) : ℂ) =
      (z + y) / √2 := by
    rw [hcos_eq, hsin_eq]; push_cast; ring
  have hterm := rotational_addition_summand_eq s z y (Real.pi / 4) m
  rw [Real.tan_pi_div_four, Complex.ofReal_one, one_pow, mul_one, hlin] at hterm
  dsimp [P]
  have hr_pow : ((-r : ℝ) : ℂ) ^ m = (r : ℂ) ^ m * (-1 : ℂ) ^ m := by
    rw [Complex.ofReal_neg, show -(r : ℂ) = (r : ℂ) * (-1 : ℂ) by ring, mul_pow]
  rw [hr_pow, hcos_eq] at *
  linear_combination (r : ℂ) ^ m * hterm

end TauCeti
