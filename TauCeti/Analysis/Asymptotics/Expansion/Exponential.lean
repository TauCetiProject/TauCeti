/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Sqrt
public import TauCeti.Analysis.Asymptotics.Expansion.Basic

import TauCeti.Analysis.SpecialFunctions.Exp.StretchedDecay

/-!
# Exponentially small functions and non-uniqueness of Poincaré expansions

This file establishes that exponentially decaying functions have the zero Poincaré asymptotic
expansion in `(z ^ n)⁻¹` at infinity, demonstrating DLMF 2.1.17 non-uniqueness: distinct
functions such as `0`, `Complex.exp (-z)`, and `Complex.exp (-Complex.sqrt z)` share the same
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
      (fun n z => (z ^ n)⁻¹) 0 (fun z => Complex.exp (-z ^ (r : ℂ))) :=
  hasAsymptoticExpansion_zero_iff.2 fun N => by
    have h : (fun z : ℂ => Complex.exp (-z ^ (r : ℂ))) =o[
        Bornology.cobounded ℂ ⊓ 𝓟 {z : ℂ | |r * Complex.arg z| ≤ π / 2 - δ}]
        fun z : ℂ => ‖(z ^ N)⁻¹‖ :=
      (TauCeti.isLittleO_cexp_neg_mul_cpow_sector (c := 1) one_pos hr (by linarith)
          (-(N : ℝ))).congr
        (fun z => by simp) fun z => by
          simp only [Real.rpow_neg (norm_nonneg z), Real.rpow_natCast, norm_inv, norm_pow]
    exact h.of_norm_right.isBigO

/-- DLMF 2.1.17: `cexp (-z)` has the zero Poincaré expansion in `(z ^ n)⁻¹` at infinity in any
closed sector `|arg z| ≤ π / 2 - δ` with `δ > 0`. -/
theorem hasAsymptoticExpansion_zero_cexp_neg_sector {δ : ℝ} (hδ : 0 < δ) :
    HasAsymptoticExpansion
      (Bornology.cobounded ℂ ⊓ 𝓟 {z : ℂ | |Complex.arg z| ≤ π / 2 - δ})
      (fun n z => (z ^ n)⁻¹) 0 (fun z => Complex.exp (-z)) := by
  simpa using hasAsymptoticExpansion_zero_cexp_neg_cpow_sector one_pos hδ

/-- DLMF 2.1.17: `cexp (-Complex.sqrt z)` has the zero Poincaré expansion in `(z ^ n)⁻¹` at
infinity in any closed sector `|arg z| ≤ π / 2 - δ` with `δ > 0`. -/
theorem hasAsymptoticExpansion_zero_cexp_neg_sqrt_sector {δ : ℝ} (hδ : 0 < δ) :
    HasAsymptoticExpansion
      (Bornology.cobounded ℂ ⊓ 𝓟 {z : ℂ | |Complex.arg z| ≤ π / 2 - δ})
      (fun n z => (z ^ n)⁻¹) 0 (fun z => Complex.exp (-Complex.sqrt z)) := by
  have h := hasAsymptoticExpansion_zero_cexp_neg_cpow_sector (r := 1 / 2) (δ := δ / 2)
    (by positivity) (half_pos hδ)
  refine (h.mono (inf_le_inf_left _ (principal_mono.mpr fun z hz => ?_))).congr'
    (Eventually.of_forall fun z => by simp [Complex.sqrt])
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
