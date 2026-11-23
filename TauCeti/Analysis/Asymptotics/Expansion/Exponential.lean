/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import TauCeti.Analysis.Asymptotics.Expansion.Basic

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Exponentially small functions and non-uniqueness of Poincaré expansions

This file establishes that exponentially decaying functions have the zero Poincaré asymptotic
expansion in `(z ^ n)⁻¹` at infinity, demonstrating DLMF 2.1.17 non-uniqueness: distinct
functions such as `0`, `Complex.exp (-z)`, and `Complex.exp (-z ^ (1 / 2 : ℂ))` share the same
Poincaré asymptotic expansion in any closed sector `|arg z| ≤ π / 2 - δ` with `δ > 0`.

## Main results

* `Asymptotics.hasAsymptoticExpansion_zero_cexp_neg_cpow_sector`: `cexp (-z ^ (r : ℂ))` has the
  zero Poincaré expansion at infinity in `{z | |r * arg z| ≤ π / 2 - δ}`.
* `Asymptotics.hasAsymptoticExpansion_zero_cexp_neg_sector` and
  `Asymptotics.hasAsymptoticExpansion_zero_cexp_neg_sqrt_sector`: DLMF 2.1.17 non-uniqueness of
  the function with a given Poincaré expansion in a closed right half-plane sector.
* `Asymptotics.hasAsymptoticExpansion_zero_exp_neg_atTop`: `Real.exp (-x)` has the zero Poincaré
  expansion along `atTop`.

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §2.1, <https://dlmf.nist.gov/2.1>.
* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974, Chapter 1.
-/

public section

open Filter Set
open scoped Real

namespace Asymptotics

/-- For any `r > 0` and `δ > 0`, `cexp (-z ^ (r : ℂ))` has the zero Poincaré expansion in
`(z ^ n)⁻¹` at infinity in the closed sector `{z | |r * arg z| ≤ π / 2 - δ}`. -/
theorem hasAsymptoticExpansion_zero_cexp_neg_cpow_sector {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) :
    HasAsymptoticExpansion
      (Bornology.cobounded ℂ ⊓ 𝓟 {z : ℂ | |r * Complex.arg z| ≤ π / 2 - δ})
      (fun n z => (z ^ n)⁻¹) 0 (fun z => Complex.exp (-z ^ (r : ℂ))) := by
  rw [hasAsymptoticExpansion_iff]
  intro N
  by_cases hδpi : δ ≤ π / 2
  · have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
    have hu : Tendsto (fun z : ℂ => ‖z‖ ^ r)
        (Bornology.cobounded ℂ ⊓ 𝓟 {z : ℂ | |r * Complex.arg z| ≤ π / 2 - δ}) atTop :=
      (tendsto_rpow_atTop hr).comp (tendsto_norm_cobounded_atTop.mono_left inf_le_left)
    have hdecay : (fun z : ℂ => Real.exp (-Real.sin δ * ‖z‖ ^ r)) =O[
        Bornology.cobounded ℂ ⊓ 𝓟 {z : ℂ | |r * Complex.arg z| ≤ π / 2 - δ}]
        fun z : ℂ => (‖z‖ ^ r) ^ (-(N : ℝ) / r) :=
      ((isLittleO_exp_neg_mul_rpow_atTop hsin (-(N : ℝ) / r)).isBigO).comp_tendsto hu
    have hnorm : (fun z : ℂ => Complex.exp (-z ^ (r : ℂ))) =O[
        Bornology.cobounded ℂ ⊓ 𝓟 {z : ℂ | |r * Complex.arg z| ≤ π / 2 - δ}]
        fun z : ℂ => Real.exp (-Real.sin δ * ‖z‖ ^ r) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [(tendsto_norm_cobounded_atTop.eventually_gt_atTop 0).filter_mono inf_le_left,
        Filter.mem_inf_of_right (mem_principal_self _)] with z hzpos hsec
      have hzne : z ≠ 0 := norm_pos_iff.mp hzpos
      have hre : (z ^ (r : ℂ)).re = ‖z‖ ^ r * Real.cos (r * Complex.arg z) := by
        rw [Complex.cpow_def_of_ne_zero hzne, Complex.exp_re]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
          Complex.log_re, Complex.mul_im, Complex.log_im, zero_add]
        rw [Real.rpow_def_of_pos hzpos, mul_comm (Complex.arg z) r]
      have hcos : Real.sin δ ≤ Real.cos (r * Complex.arg z) := by
        rw [← Real.cos_pi_div_two_sub, ← Real.cos_abs (r * Complex.arg z)]
        exact Real.strictAntiOn_cos.antitoneOn
          ⟨abs_nonneg _, hsec.trans (by linarith)⟩
          ⟨by linarith, by linarith⟩ hsec
      rw [one_mul, Complex.norm_exp, Complex.neg_re, hre,
        Real.norm_of_nonneg (Real.exp_nonneg _)]
      exact Real.exp_le_exp.mpr (by nlinarith [Real.rpow_pos_of_pos hzpos r])
    rw [← isBigO_norm_right]
    refine (hnorm.trans hdecay).congr' (Eventually.of_forall fun z => by simp) ?_
    filter_upwards [(tendsto_norm_cobounded_atTop.eventually_gt_atTop 0).filter_mono inf_le_left]
      with z hzpos
    rw [← Real.rpow_mul hzpos.le, mul_div_cancel₀ _ hr.ne', Real.rpow_neg hzpos.le,
      Real.rpow_natCast, norm_inv, norm_pow]
  · have hemp : {z : ℂ | |r * Complex.arg z| ≤ π / 2 - δ} = ∅ := by
      ext z
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      linarith [abs_nonneg (r * Complex.arg z)]
    rw [hemp, principal_empty, inf_bot_eq]
    exact isBigO_bot _ _

/-- DLMF 2.1.17: `cexp (-z)` has the zero Poincaré expansion in `(z ^ n)⁻¹` at infinity in any
closed sector `|arg z| ≤ π / 2 - δ` with `δ > 0`. -/
theorem hasAsymptoticExpansion_zero_cexp_neg_sector {δ : ℝ} (hδ : 0 < δ) :
    HasAsymptoticExpansion
      (Bornology.cobounded ℂ ⊓ 𝓟 {z : ℂ | |Complex.arg z| ≤ π / 2 - δ})
      (fun n z => (z ^ n)⁻¹) 0 (fun z => Complex.exp (-z)) := by
  simpa using hasAsymptoticExpansion_zero_cexp_neg_cpow_sector one_pos hδ

/-- DLMF 2.1.17: `cexp (-z ^ (1 / 2 : ℂ))` has the zero Poincaré expansion in `(z ^ n)⁻¹` at
infinity in any closed sector `|arg z| ≤ π / 2 - δ` with `δ > 0`. -/
theorem hasAsymptoticExpansion_zero_cexp_neg_sqrt_sector {δ : ℝ} (hδ : 0 < δ) :
    HasAsymptoticExpansion
      (Bornology.cobounded ℂ ⊓ 𝓟 {z : ℂ | |Complex.arg z| ≤ π / 2 - δ})
      (fun n z => (z ^ n)⁻¹) 0 (fun z => Complex.exp (-z ^ (1 / 2 : ℂ))) := by
  have h := hasAsymptoticExpansion_zero_cexp_neg_cpow_sector (r := 1 / 2) (δ := δ / 2)
    (by positivity) (half_pos hδ)
  refine (h.mono (inf_le_inf_left _ (principal_mono.mpr fun z hz => ?_))).congr'
    (Eventually.of_forall fun z => by norm_num)
  simp only [mem_ofPred_eq] at hz ⊢
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / 2)]
  linarith [Real.pi_pos]

/-- `Real.exp (-x)` has the zero Poincaré expansion in `(x ^ n)⁻¹` along `atTop`. -/
theorem hasAsymptoticExpansion_zero_exp_neg_atTop :
    HasAsymptoticExpansion atTop (fun n (x : ℝ) => (x ^ n)⁻¹) 0 (fun x => Real.exp (-x)) := by
  rw [hasAsymptoticExpansion_iff]
  intro N
  have h := (isLittleO_exp_neg_mul_rpow_atTop one_pos (-(N : ℝ))).isBigO
  refine h.congr' (Eventually.of_forall fun x => by simp) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.rpow_neg hx.le, Real.rpow_natCast]

end Asymptotics
