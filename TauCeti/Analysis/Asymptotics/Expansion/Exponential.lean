/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Asymptotics.Expansion.Basic

import TauCeti.Analysis.SpecialFunctions.Exp.StretchedDecay
import TauCeti.Analysis.SpecialFunctions.Pow.Sector

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
    have hdecay : (fun z : ℂ => Real.exp (-Real.sin δ * ‖z‖ ^ r)) =O[
        Bornology.cobounded ℂ ⊓ 𝓟 {z : ℂ | |r * Complex.arg z| ≤ π / 2 - δ}]
        fun z : ℂ => ‖z‖ ^ (-(N : ℝ)) :=
      ((TauCeti.isLittleO_exp_neg_mul_rpow_rpow_atTop hsin hr (-(N : ℝ))).isBigO).comp_tendsto
        (tendsto_norm_cobounded_atTop.mono_left inf_le_left)
    have hnorm : (fun z : ℂ => Complex.exp (-z ^ (r : ℂ))) =O[
        Bornology.cobounded ℂ ⊓ 𝓟 {z : ℂ | |r * Complex.arg z| ≤ π / 2 - δ}]
        fun z : ℂ => Real.exp (-Real.sin δ * ‖z‖ ^ r) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [Filter.mem_inf_of_right (mem_principal_self _)] with z hsec
      have hcone := TauCeti.cos_mul_norm_rpow_le_re_exp_mul_cpow (z := z) (y := r) (φ := 0)
        (δ := π / 2 - δ) (by simpa [sub_zero, mul_comm] using hsec) (by linarith [Real.pi_pos])
      simp only [neg_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul,
        Real.cos_pi_div_two_sub] at hcone
      rw [one_mul, Complex.norm_exp, Complex.neg_re, Real.norm_of_nonneg (Real.exp_nonneg _)]
      exact Real.exp_le_exp.mpr (by linarith)
    rw [← isBigO_norm_right]
    refine (hnorm.trans hdecay).congr' (Eventually.of_forall fun z => by simp)
      (Eventually.of_forall fun z => ?_)
    dsimp only
    rw [Real.rpow_neg (norm_nonneg z), Real.rpow_natCast, norm_inv, norm_pow]
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
