/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import Mathlib.Analysis.Fourier.PoissonSummation
public import TauCeti.Analysis.Fourier.ExpNegAbs
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Probability.Distributions.Cauchy.Basic
public import TauCeti.Analysis.SpecialFunctions.Exp.LatticeSum

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
The Fourier-transform evaluation is reused from `TauCeti.Probability`
`fourier_exp_neg_mul_abs_eq_cauchyPDFReal_zero_loc`. The exponential decay
argument remains local so as not to duplicate a general asymptotics API.
-/

public section

namespace TauCeti

open MeasureTheory Set Filter Asymptotics
open scoped BigOperators FourierTransform

noncomputable section

/-- A two-sided complex exponential decays faster than every real power at infinity. -/
private theorem cexp_neg_mul_abs_isLittleO_rpow_cocompact
    {a : ℝ} (ha : 0 < a) (s : ℝ) :
    (fun x : ℝ => Complex.exp ((-(a * |x|) : ℝ) : ℂ))
      =o[cocompact ℝ] (fun x : ℝ => |x| ^ s) := by
  apply IsLittleO.of_norm_left
  simp only [Complex.norm_exp, Complex.ofReal_re]
  rw [cocompact_eq_atBot_atTop, isLittleO_sup]
  constructor
  · have h := (isLittleO_exp_neg_mul_rpow_atTop ha s).comp_tendsto
      tendsto_neg_atBot_atTop
    refine h.congr' ?_ ?_
    · filter_upwards [eventually_lt_atBot 0] with x hx
      simp [abs_of_neg hx]
    · filter_upwards [eventually_lt_atBot 0] with x hx
      simp [abs_of_neg hx]
  · refine (isLittleO_exp_neg_mul_rpow_atTop ha s).congr' ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx
      simp [abs_of_pos hx]
    · filter_upwards [eventually_gt_atTop 0] with x hx
      simp [abs_of_pos hx]


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
  have hfDecay : f =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-2 : ℝ)) :=
    (cexp_neg_mul_abs_isLittleO_rpow_cocompact hscale (-2)).isBigO
  let γ : NNReal := ⟨y, hy.le⟩
  -- Make the real coercion explicit rather than relying on unfolding the NNReal coercion.
  have hγ_coe : (γ : ℝ) = y := by
    change ((⟨y, hy.le⟩ : NNReal) : ℝ) = y
    exact NNReal.coe_mk y hy.le
  have hγ : γ ≠ 0 := by
    have hpos : (0 : ℝ) < (γ : ℝ) := by rw [hγ_coe]; exact hy
    exact (NNReal.coe_pos.mp hpos).ne'
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
    have hden : y ^ 2 + x ^ 2 ≠ 0 := by positivity
    have hden' : x ^ 2 + y ^ 2 ≠ 0 := by positivity
    change Real.pi⁻¹ * y * (x ^ 2 + y ^ 2)⁻¹ =
      y / (Real.pi * (y ^ 2 + x ^ 2))
    field_simp [Real.pi_ne_zero, hden, hden']; ring
  have hFourierDecay : (𝓕 f) =O[cocompact ℝ]
      (fun x : ℝ => |x| ^ (-2 : ℝ)) := by
    rw [hFourierCauchy]
    exact TauCeti.Probability.cauchyPDFReal_zero_loc_isBigO_rpow_neg_two γ
  have hPoisson := Real.tsum_eq_tsum_fourier_of_rpow_decay
    hfContinuous (by norm_num : (1 : ℝ) < 2) hfDecay hFourierDecay 0
  simpa only [f, zero_add, hFourier, Int.cast_zero, QuotientAddGroup.mk_zero,
    fourier_eval_zero, mul_one] using hPoisson

/-- **Real Cauchy Poisson identity.** Both sides are real-valued, and the complex-valued
Fourier identity is used only in the proof. -/
theorem tsum_exp_neg_mul_abs_int_eq_tsum_div {y : ℝ} (hy : 0 < y) :
    (∑' n : ℤ, Real.exp (-(2 * Real.pi * y * |(n : ℝ)|))) =
      ∑' n : ℤ, y / (Real.pi * (y ^ 2 + (n : ℝ) ^ 2)) := by
  apply Complex.ofReal_injective
  calc
    ((∑' n : ℤ, Real.exp (-(2 * Real.pi * y * |(n : ℝ)|)) : ℝ) : ℂ) =
        ∑' n : ℤ, Complex.exp ((-(2 * Real.pi * y * |(n : ℝ)|) : ℝ) : ℂ) := by
      calc
        _ = ∑' n : ℤ, (Real.exp (-(2 * Real.pi * y * |(n : ℝ)|)) : ℂ) :=
          Complex.ofReal_tsum _
        _ = _ := by
          apply tsum_congr
          intro n
          rw [Complex.ofReal_exp]
    _ = ∑' n : ℤ, ((y / (Real.pi * (y ^ 2 + (n : ℝ) ^ 2)) : ℝ) : ℂ) :=
      tsum_cexp_neg_mul_abs_int_eq_tsum_div hy
    _ = ((∑' n : ℤ, y / (Real.pi * (y ^ 2 + (n : ℝ) ^ 2)) : ℝ) : ℂ) :=
      (Complex.ofReal_tsum _).symm

/-- **Cauchy lattice sum.** Evaluating the Poisson identity gives the full sum
of `1 / (y² + n²)` over the integers. -/
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
