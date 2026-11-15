/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Gaussian–Laplace moment integrals on `(0, ∞)`

This file develops the analytic properties of the Gaussian–Laplace moment integral

  `I(s, z) = ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * cexp (-u ^ 2 / 2 - z * u)`,

which is the Mellin transform of `u ↦ exp(-u² / 2 - z u)` and (up to the prefactor
`exp(-z² / 4) / Γ(s)`) represents the parabolic cylinder function `U(s - 1 / 2, z)` on the right
half-plane `0 < Re s` (DLMF 12.5.1).

## Main results

* `TauCeti.norm_cpow_mul_cexp_neg_mul_sq_sub_mul`,
  `TauCeti.norm_cpow_mul_cexp_neg_sq_div_two_sub_mul`: pointwise norm of
  `u^{s - 1} exp(-q u² - z u)` and of its `q = 1 / 2` specialization for `0 < u`.
* `TauCeti.integrableOn_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi`,
  `TauCeti.integrableOn_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi`,
  `TauCeti.integrableOn_rpow_mul_rexp_neg_sq_div_two_sub_mul_Ioi`,
  `TauCeti.integrableOn_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi_iff`: integrability for
  `0 < Re s` and `0 < Re q`, the real specialization, and the exact criterion `0 < Re s` for
  `q = 1 / 2`.
* `TauCeti.differentiable_integral_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi`: `z ↦ I(s, z)` is
  entire on `ℂ` for every `s : ℂ` (vanishing identically when `Re s ≤ 0`).
* `TauCeti.differentiableOn_integral_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi`: `s ↦ I(s, z)` is
  holomorphic on `{s : ℂ | 0 < Re s}` for every `z : ℂ`.
* `TauCeti.integral_cpow_mul_cexp_neg_div_sq_div_two_sub_mul_Ioi`: positive dilation identity for
  `0 < c` and all `s z : ℂ`.

## References

* *NIST Digital Library of Mathematical Functions*, [§12.5](https://dlmf.nist.gov/12.5).
-/

public section

open Complex Real MeasureTheory Set Filter Asymptotics
open scoped Topology

namespace TauCeti

/-- Pointwise norm of the general Gaussian–Laplace integrand `u^{s - 1} exp(-q u² - z u)` for
`0 < u`. -/
theorem norm_cpow_mul_cexp_neg_mul_sq_sub_mul (s q z : ℂ) {u : ℝ} (hu : 0 < u) :
    ‖(u : ℂ) ^ (s - 1) * cexp (-q * (u : ℂ) ^ 2 - z * u)‖ =
      u ^ (s.re - 1) * rexp (-q.re * u ^ 2 - z.re * u) := by
  have hre : (-q * (u : ℂ) ^ 2 - z * u).re = -q.re * u ^ 2 - z.re * u := by
    simp [← Complex.ofReal_pow]
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.norm_exp, Complex.sub_re,
    Complex.one_re, hre]

/-- Pointwise norm of the standard Gaussian–Laplace integrand `u^{s - 1} exp(-u² / 2 - z u)` for
`0 < u`. -/
theorem norm_cpow_mul_cexp_neg_sq_div_two_sub_mul (s z : ℂ) {u : ℝ} (hu : 0 < u) :
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
theorem integrableOn_rpow_mul_rexp_neg_sq_div_two_sub_mul_Ioi {σ : ℝ} (hσ : 0 < σ) (b : ℝ) :
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
`z ↦ ∫₀^∞ u^{s - 1} exp(-u² / 2 - z u) du` is entire on `ℂ` (for `Re s ≤ 0`, the Bochner integral
vanishes identically because the integrand is not integrable). -/
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

/-- For every `z : ℂ`, the Gaussian–Laplace integral
`s ↦ ∫₀^∞ u^{s - 1} exp(-u² / 2 - z u) du` is holomorphic on `{s : ℂ | 0 < Re s}`. -/
theorem differentiableOn_integral_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi (z : ℂ) :
    DifferentiableOn ℂ
      (fun s : ℂ => ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * cexp (-(u : ℂ) ^ 2 / 2 - z * u))
      {s : ℂ | 0 < s.re} := by
  let f : ℝ → ℂ := fun u => cexp (-(u : ℂ) ^ 2 / 2 - z * u)
  have hmellin : (fun s : ℂ => ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * f u) = mellin f := by
    ext s; simp only [mellin, smul_eq_mul]
  rw [hmellin]
  have hf_cont : Continuous f := by fun_prop
  have hf_loc : LocallyIntegrableOn f (Ioi 0) :=
    hf_cont.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have hf_top : f =O[atTop] fun u : ℝ => rexp (-1 * u) := by
    refine isBigO_iff.mpr ⟨rexp ((z.re - 1) ^ 2 / 2), Eventually.of_forall fun u => ?_⟩
    have hre : (-(u : ℂ) ^ 2 / 2 - z * u).re = -u ^ 2 / 2 - z.re * u := by
      simp [← Complex.ofReal_pow]
    have hsq : -u ^ 2 / 2 - z.re * u ≤ (z.re - 1) ^ 2 / 2 + -1 * u := by
      linarith [sq_nonneg (u + (z.re - 1))]
    rw [Complex.norm_exp, hre, Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
    exact Real.exp_le_exp.mpr hsq
  have hf_bot : f =O[𝓝[>] 0] (· ^ (-(0 : ℝ))) := by
    simp_rw [neg_zero, Real.rpow_zero]
    exact isBigO_const_of_tendsto
      (hf_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) one_ne_zero
  intro s hs
  exact (mellin_differentiableAt_of_isBigO_rpow_exp zero_lt_one hf_loc hf_top hf_bot
    hs).differentiableWithinAt

/-- Positive dilation of the Gaussian–Laplace integral: for `0 < c` and all `s z : ℂ` (including
`Re s ≤ 0`, where both Bochner integrals vanish),
`∫₀^∞ u^{s - 1} exp(-(u / c)² / 2 - z u) du = c^s ∫₀^∞ v^{s - 1} exp(-v² / 2 - z c v) dv`. -/
theorem integral_cpow_mul_cexp_neg_div_sq_div_two_sub_mul_Ioi {c : ℝ} (hc : 0 < c) (s z : ℂ) :
    (∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * cexp (-((u : ℂ) / c) ^ 2 / 2 - z * u)) =
      (c : ℂ) ^ s *
        ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (s - 1) * cexp (-(v : ℂ) ^ 2 / 2 - z * c * v) := by
  let f : ℝ → ℂ := fun v => cexp (-(v : ℂ) ^ 2 / 2 - z * c * v)
  have hc_ne : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hscale := mellin_comp_mul_left f s (inv_pos.mpr hc)
  simp only [mellin, f, smul_eq_mul] at hscale
  have harg : (c : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hc.le]
    exact Real.pi_pos.ne
  have hcpow : ((c⁻¹ : ℝ) : ℂ) ^ (-s) = (c : ℂ) ^ s := by
    rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg, Complex.cpow_neg, inv_inv]
  rw [hcpow] at hscale
  refine (setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_).trans hscale
  congr 2
  push_cast
  field_simp

end TauCeti
