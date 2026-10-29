/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Exp.LatticeSum
import TauCeti.Probability.Distributions.Cauchy.Basic

/-!
# Poisson summation for the Cauchy kernel

For `y > 0`, Poisson summation identifies the two-sided exponential lattice
sum with the lattice sum of its Cauchy Fourier transform. Combined with the
geometric lattice series, this evaluates the full Cauchy lattice sum.

## Main results

* `TauCeti.tsum_exp_neg_mul_abs_int_eq_tsum_div`: the real-valued Poisson identity.
* `TauCeti.tsum_int_inv_sq_add_sq`: the Cauchy lattice sum in exponential form.

## Provenance

Adapted from `ForTauCeti/Analysis/Fourier/Poisson/CauchyLattice.lean`
in AIQ-Kitware/aiq-dkps-formalization (Apache-2.0; Jon Crall and GPT 5.6 High).
-/

public section

namespace TauCeti

open MeasureTheory Set Filter Asymptotics
open scoped BigOperators FourierTransform

noncomputable section

/-- **Poisson summation for the Cauchy lattice.** For `y > 0`, the lattice sum of
`exp (-2π y |n|)` is the sum of its sampled Cauchy Fourier transform. -/
private theorem tsum_cexp_neg_mul_abs_int_eq_tsum_div {y : ℝ} (hy : 0 < y) :
    (∑' n : ℤ,
      Complex.exp ((-(2 * Real.pi * y * |(n : ℝ)|) : ℝ) : ℂ)) =
    ∑' n : ℤ, ((y / (Real.pi * (y ^ 2 + (n : ℝ) ^ 2)) : ℝ) : ℂ) := by
  let f : ℝ → ℂ := fun t => Complex.exp ((-(2 * Real.pi * y * |t|) : ℝ) : ℂ)
  have hscale : 0 < 2 * Real.pi * y := by positivity
  have hfContinuous : Continuous f := by
    dsimp only [f]
    fun_prop
  -- Check the Poisson decay hypothesis at the two ends of the real line.
  have hfLittleO : f =o[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
    apply IsLittleO.of_norm_left
    simp only [f, Complex.norm_exp, Complex.ofReal_re]
    rw [cocompact_eq_atBot_atTop, isLittleO_sup]
    constructor
    · have h := (isLittleO_exp_neg_mul_rpow_atTop hscale (-2)).comp_tendsto
        tendsto_neg_atBot_atTop
      refine h.congr' ?_ ?_
      · filter_upwards [eventually_lt_atBot 0] with x hx
        simp [abs_of_neg hx]
      · filter_upwards [eventually_lt_atBot 0] with x hx
        simp [abs_of_neg hx]
    · refine (isLittleO_exp_neg_mul_rpow_atTop hscale (-2)).congr' ?_ ?_
      · filter_upwards [eventually_gt_atTop 0] with x hx
        simp [abs_of_pos hx]
      · filter_upwards [eventually_gt_atTop 0] with x hx
        simp [abs_of_pos hx]
  have hfDecay : f =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) := hfLittleO.isBigO
  set γ : NNReal := ⟨y, hy.le⟩ with hγdef
  have hγ_coe : (γ : ℝ) = y := by
    calc
      (γ : ℝ) = ((⟨y, hy.le⟩ : NNReal) : ℝ) :=
        congrArg (fun u : NNReal => (u : ℝ)) hγdef
      _ = y := NNReal.coe_mk y hy.le
  have hγ : γ ≠ 0 := by
    intro hz
    have hzero : (γ : ℝ) = 0 := congrArg (fun u : NNReal => (u : ℝ)) hz
    rw [hγ_coe] at hzero
    exact hy.ne' hzero
  have hfun : f = fun t : ℝ =>
      (Real.exp (-(2 * Real.pi * (γ : ℝ) * |t|)) : ℂ) := by
    funext t
    simp only [f, Complex.ofReal_exp, hγ_coe]
  have hFourierCauchy : 𝓕 f = fun x : ℝ =>
      (ProbabilityTheory.cauchyPDFReal 0 γ x : ℂ) := by
    rw [hfun]
    exact funext (TauCeti.Probability.fourier_exp_neg_mul_abs_eq_cauchyPDFReal_zero_loc hγ)
  have hFourier : 𝓕 f = fun x : ℝ =>
      ((y / (Real.pi * (y ^ 2 + x ^ 2)) : ℝ) : ℂ) := by
    rw [hFourierCauchy]
    funext x
    congr 1
    rw [ProbabilityTheory.cauchyPDFReal_def]
    simp only [sub_zero, hγ_coe]
    have hden : x ^ 2 + y ^ 2 ≠ 0 := by positivity
    rw [add_comm (y ^ 2) (x ^ 2)]
    field_simp [Real.pi_ne_zero, hden]
  have hFourierDecay : (𝓕 f) =O[cocompact ℝ]
      (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
    rw [hFourierCauchy]
    refine IsBigO.of_norm_left ?_
    simpa only [Complex.norm_real] using
      (TauCeti.Probability.cauchyPDFReal_zero_loc_isBigO_rpow_neg_two γ).norm_left
  have hPoisson := Real.tsum_eq_tsum_fourier_of_rpow_decay
    hfContinuous (by norm_num : (1 : ℝ) < 2) hfDecay hFourierDecay 0
  simpa only [f, zero_add, hFourier, Int.cast_zero, QuotientAddGroup.mk_zero,
    fourier_eval_zero, mul_one] using hPoisson

/-- **Real Cauchy Poisson identity.** For `y > 0`, the sum over integers of
`exp (-2π y |n|)` equals the sum of `y / (π (y² + n²))`. -/
theorem tsum_exp_neg_mul_abs_int_eq_tsum_div {y : ℝ} (hy : 0 < y) :
    (∑' n : ℤ, Real.exp (-(2 * Real.pi * y * |(n : ℝ)|))) =
      ∑' n : ℤ, y / (Real.pi * (y ^ 2 + (n : ℝ) ^ 2)) := by
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_tsum, Complex.ofReal_exp] using
    (tsum_cexp_neg_mul_abs_int_eq_tsum_div hy)

/-- **Cauchy lattice sum.** For `y > 0`, the sum over integers of
`1 / (y² + n²)` equals `(π / y) * (1 + exp (-2πy)) / (1 - exp (-2πy))`. -/
theorem tsum_int_inv_sq_add_sq {y : ℝ} (hy : 0 < y) :
    (∑' n : ℤ, (y ^ 2 + (n : ℝ) ^ 2)⁻¹) =
      (Real.pi / y) *
        ((1 + Real.exp (-(2 * Real.pi * y))) /
          (1 - Real.exp (-(2 * Real.pi * y)))) := by
  have hscale : 0 < 2 * Real.pi * y := by positivity
  have hPoissonReal := tsum_exp_neg_mul_abs_int_eq_tsum_div hy
  -- Pull out the common scalar in the Cauchy sum before rearranging.
  have hscaled :
      (∑' n : ℤ, y / (Real.pi * (y ^ 2 + (n : ℝ) ^ 2))) =
        (y / Real.pi) * ∑' n : ℤ, (y ^ 2 + (n : ℝ) ^ 2)⁻¹ := by
    calc
      (∑' n : ℤ, y / (Real.pi * (y ^ 2 + (n : ℝ) ^ 2))) =
          ∑' n : ℤ, (y / Real.pi) * (y ^ 2 + (n : ℝ) ^ 2)⁻¹ := by
        apply tsum_congr
        intro n
        have hden : y ^ 2 + (n : ℝ) ^ 2 ≠ 0 := by
          nlinarith [sq_nonneg (n : ℝ)]
        field_simp [Real.pi_ne_zero, hden]
      _ = (y / Real.pi) * ∑' n : ℤ, (y ^ 2 + (n : ℝ) ^ 2)⁻¹ :=
        tsum_mul_left
  have hgeom :
      (∑' n : ℤ, Real.exp (-(2 * Real.pi * y * |(n : ℝ)|))) =
        (1 + Real.exp (-(2 * Real.pi * y))) /
          (1 - Real.exp (-(2 * Real.pi * y))) := by
    exact tsum_int_exp_neg_mul_abs hscale
  have heq :
      (y / Real.pi) * ∑' n : ℤ, (y ^ 2 + (n : ℝ) ^ 2)⁻¹ =
        (1 + Real.exp (-(2 * Real.pi * y))) /
          (1 - Real.exp (-(2 * Real.pi * y))) := by
    rw [← hscaled, ← hPoissonReal]
    exact hgeom
  calc
    (∑' n : ℤ, (y ^ 2 + (n : ℝ) ^ 2)⁻¹) =
        (Real.pi / y) * ((y / Real.pi) *
          ∑' n : ℤ, (y ^ 2 + (n : ℝ) ^ 2)⁻¹) := by
      field_simp [Real.pi_ne_zero, hy.ne']
    _ = (Real.pi / y) *
          ((1 + Real.exp (-(2 * Real.pi * y))) /
            (1 - Real.exp (-(2 * Real.pi * y)))) := by
      rw [heq]

end

end TauCeti
