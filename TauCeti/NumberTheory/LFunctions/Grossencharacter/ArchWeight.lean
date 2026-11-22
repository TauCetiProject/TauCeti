/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Harmonic
public import TauCeti.NumberTheory.LFunctions.Theta.Surface.Haar
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.NumberTheory.LFunctions.Theta.GammaIntegral

/-!
# Regularity, radial scaling, and Deligne gamma integral for `Grossencharacter.archWeight`

This module complements `TauCeti.NumberTheory.LFunctions.Grossencharacter.Harmonic` with
additional properties of the archimedean parameter weight
`χ.archWeight y = ∏_w y_w ^ (P_w / 2)` (`P_w = χ.harmonicExponent w`):

* regularity (`continuous_archWeight`, `measurable_archWeight`) and triviality specializations
  (`archWeight_of_harmonicDegree_eq_zero`, `archWeight_of_toHeckeCharacter_eq_one`, and ray class
  specializations);
* absorption of the Hecke-lemma factor `∏_w y_w ^ (-P_w)` into `archWeight y⁻¹`
  (`archWeight_mul_prod_inv_pow`, Neukirch VII (8.5));
* radial scaling under `surfaceScale x t` (`archWeight_surfaceScale`, Neukirch VII (8.3)),
  shifting the radial Mellin variable `s / 2` by `Tr(p) / (2 [K : ℚ])` (and `s` by
  `Tr(p) / [K : ℚ]`);
* decomposition of `∏_w Γ_ℝ(mult w · s + P_w)` into Deligne's `Γ_ℝ` and `Γ_ℂ` factors
  (`prod_Gammaℝ_mult_mul_add_harmonicExponent`) and the resulting closed form of the weighted
  archimedean gamma integral (`integral_archWeight_mul_archGaussian_mul_archNorm_cpow`).

## Main results

* `TauCeti.LFunctions.Grossencharacter.archWeight_surfaceScale`: radial-scaling law under
  `surfaceScale`.
* `TauCeti.LFunctions.Grossencharacter.archWeight_mul_prod_inv_pow`: absorption of the Hecke-lemma
  weight `∏_w y_w ^ (-P_w)` into `archWeight y⁻¹`.
* `TauCeti.LFunctions.Grossencharacter.prod_Gammaℝ_mult_mul_add_harmonicExponent`: decomposition of
  `∏_w Γ_ℝ(mult w · s + P_w)` into Deligne's `Γ_ℝ` and `Γ_ℂ` factors.
* `TauCeti.LFunctions.Grossencharacter.integral_archWeight_mul_archGaussian_mul_archNorm_cpow`:
  Deligne `Γ_ℝ`/`Γ_ℂ` form of the weighted archimedean gamma integral.

## References

* E. Hecke, *Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen
  (Zweite Mitteilung)*, Math. Z. **6** (1920), 11–51.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §§7–8.
-/

public section

noncomputable section

open Complex MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  TauCeti.NumberField.mixedEmbedding
open scoped Real

namespace TauCeti.LFunctions.Grossencharacter

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-! ### Additional basic, regularity, and scaling properties of `archWeight` -/

/-- When `harmonicDegree` vanishes, `archWeight` is identically `1`. -/
theorem archWeight_of_harmonicDegree_eq_zero {χ : Grossencharacter K 𝔪}
    (h : χ.harmonicDegree = 0) (y : realSpace K) : χ.archWeight y = 1 := by
  have hw := χ.harmonicDegree_eq_zero_iff.mp h
  simp [archWeight_def, hw]

/-- A ray-class presentation with trivial archimedean modulus has constant weight `1`. -/
theorem archWeight_ofRayClassCharacter_of_infinitePart_eq_empty (h𝔪 : 𝔪.infinitePart = ∅)
    (η : RayClassCharacter 𝔪) (y : realSpace K) :
    (ofRayClassCharacter η).archWeight y = 1 :=
  archWeight_of_harmonicDegree_eq_zero
    (harmonicDegree_ofRayClassCharacter_of_infinitePart_eq_empty h𝔪 η) y

/-- At the trivial modulus, every ray class character has constant weight `1`. -/
@[simp]
theorem archWeight_ofRayClassCharacter_of_modulus_one (η : RayClassCharacter (Modulus.one K))
    (y : realSpace K) : (ofRayClassCharacter η).archWeight y = 1 :=
  archWeight_of_harmonicDegree_eq_zero (harmonicDegree_ofRayClassCharacter_of_modulus_one η) y

/-- Any presentation of the trivial Hecke character has `archWeight` identically `1`. -/
theorem archWeight_of_toHeckeCharacter_eq_one {χ : Grossencharacter K 𝔪}
    (hχ : χ.toHeckeCharacter = 1) (y : realSpace K) : χ.archWeight y = 1 :=
  archWeight_of_harmonicDegree_eq_zero (harmonicDegree_of_toHeckeCharacter_eq_one hχ) y

/-- On nonnegative parameters, `archWeight y` is `∏_w √(y_w) ^ P_w`. -/
theorem archWeight_eq_prod_sqrt_pow (χ : Grossencharacter K 𝔪) {y : realSpace K}
    (hy : ∀ w, 0 ≤ y w) :
    χ.archWeight y = ∏ w : InfinitePlace K, √(y w) ^ χ.harmonicExponent w := by
  rw [archWeight_def]
  exact Finset.prod_congr rfl fun w _ ↦ (Real.pow_sqrt_eq_rpow (hy w) _).symm

@[fun_prop]
theorem continuous_archWeight (χ : Grossencharacter K 𝔪) : Continuous χ.archWeight := by
  rw [funext χ.archWeight_def]
  exact continuous_finsetProd _ fun w _ ↦ (continuous_apply w).rpow_const fun _ ↦
    Or.inr (by positivity)

@[fun_prop]
theorem measurable_archWeight (χ : Grossencharacter K 𝔪) : Measurable χ.archWeight :=
  χ.continuous_archWeight.measurable

/-- Multiplying `archWeight y` by the Hecke-lemma factor `∏_w y_w ^ (-P_w)` gives
`archWeight y⁻¹` (Neukirch VII (8.5)). -/
theorem archWeight_mul_prod_inv_pow (χ : Grossencharacter K 𝔪) {y : realSpace K}
    (hy : ∀ w, 0 ≤ y w) :
    χ.archWeight y * (∏ w : InfinitePlace K, (y w)⁻¹ ^ χ.harmonicExponent w) =
      χ.archWeight y⁻¹ := by
  rw [archWeight_def, archWeight_def, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rcases (hy w).eq_or_lt with hy0 | hypos
  · rw [Pi.inv_apply, ← hy0, inv_zero]
    rcases Nat.eq_zero_or_pos (χ.harmonicExponent w) with hp | hp
    · simp [hp]
    · have hp' : ((χ.harmonicExponent w : ℝ) / 2) ≠ 0 := by positivity
      rw [Real.zero_rpow hp', zero_mul]
  · have h1 : (y w)⁻¹ ^ χ.harmonicExponent w =
        ((y w)⁻¹ ^ ((χ.harmonicExponent w : ℝ) / 2)) ^ 2 := by
      rw [Real.rpow_div_two_sq (inv_nonneg.mpr hypos.le), Real.rpow_natCast]
    have h2 :
        y w ^ ((χ.harmonicExponent w : ℝ) / 2) *
          (y w)⁻¹ ^ ((χ.harmonicExponent w : ℝ) / 2) = 1 := by
      rw [← Real.mul_rpow hypos.le (inv_nonneg.mpr hypos.le), mul_inv_cancel₀ hypos.ne',
        Real.one_rpow]
    rw [Pi.inv_apply, h1, sq, ← mul_assoc, h2, one_mul]

/-- **Radial scaling of `archWeight`** (Neukirch VII (8.3)): for `0 ≤ t`, scaling by
`surfaceScale x t` multiplies `archWeight x` by `t ^ (Tr(p) / (2 [K : ℚ]))`. -/
theorem archWeight_surfaceScale (χ : Grossencharacter K 𝔪) (x : realSpace K) {t : ℝ}
    (ht : 0 ≤ t) :
    χ.archWeight (surfaceScale x t) =
      χ.archWeight x * t ^ ((χ.harmonicDegree : ℝ) / (2 * Module.finrank ℚ K)) := by
  have hsplit : χ.archWeight (surfaceScale x t) =
      χ.archWeight x *
        ∏ w : InfinitePlace K, t ^ ((χ.harmonicExponent w : ℝ) / (2 * Module.finrank ℚ K)) := by
    rw [archWeight_def, archWeight_def, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [surfaceScale_apply, mul_comm (x w), Real.mul_rpow_of_nonneg_left (Real.rpow_nonneg ht _),
      mul_comm, ← Real.rpow_mul ht]
    congr 2
    ring
  rw [hsplit]
  congr 1
  rw [← Real.rpow_sum_of_nonneg ht fun _ _ ↦ by positivity, ← Finset.sum_div, ← Nat.cast_sum,
    ← harmonicDegree_def]

/-! ### Deligne `Γ_ℝ` / `Γ_ℂ` form of the weighted archimedean gamma integral -/

open scoped Classical in
/-- Decomposition of `∏_w Γ_ℝ(mult w · s + P_w)` into Deligne's `Γ_ℝ` and `Γ_ℂ` factors across the
real and complex infinite places of `K`. -/
theorem prod_Gammaℝ_mult_mul_add_harmonicExponent (χ : Grossencharacter K 𝔪) (s : ℂ) :
    (∏ w : InfinitePlace K, Gammaℝ ((mult w : ℂ) * s + χ.harmonicExponent w)) =
      ((2 : ℂ) ^ (s - 1)) ^ nrComplexPlaces K *
        (2 : ℂ) ^
          ((∑ w : {w : InfinitePlace K // w.IsComplex}, (χ.harmonicExponent w.val : ℂ)) / 2) *
        ((∏ w : {w : InfinitePlace K // w.IsReal}, Gammaℝ (s + χ.harmonicExponent w.val)) *
          ∏ w : {w : InfinitePlace K // w.IsComplex},
            Gammaℂ (s + (χ.harmonicExponent w.val : ℂ) / 2)) :=
  prod_Gammaℝ_mult_mul_add s fun w ↦ (χ.harmonicExponent w : ℂ)

open scoped Classical in
/-- **The weighted archimedean gamma integral** of a Grossencharacter in Deligne `Γ_ℝ` and `Γ_ℂ`
form (Neukirch VII §8): for `∀ w, 0 < mult w * s.re + P_w`, integrating
`(χ.archWeight y : ℂ) * archGaussian y x * (archNorm y : ℂ) ^ (s / 2)` over `archHaar K` yields
the shifted gamma product times `(∏_w |x_w| ^ P_w)⁻¹ |N(x)| ^ (-s)` (when
`mixedEmbedding.norm x = 0`, both sides vanish). -/
theorem integral_archWeight_mul_archGaussian_mul_archNorm_cpow {χ : Grossencharacter K 𝔪}
    (x : mixedSpace K) {s : ℂ}
    (hs : ∀ w, 0 < (mult w : ℝ) * s.re + χ.harmonicExponent w) :
    ∫ y, (χ.archWeight y : ℂ) * archGaussian y x * (archNorm y : ℂ) ^ (s / 2) ∂archHaar K =
      ((2 : ℂ) ^ (s - 1)) ^ nrComplexPlaces K *
        (2 : ℂ) ^
          ((∑ w : {w : InfinitePlace K // w.IsComplex}, (χ.harmonicExponent w.val : ℂ)) / 2) *
        ((∏ w : {w : InfinitePlace K // w.IsReal}, Gammaℝ (s + χ.harmonicExponent w.val)) *
          ∏ w : {w : InfinitePlace K // w.IsComplex},
            Gammaℂ (s + (χ.harmonicExponent w.val : ℂ) / 2)) *
        ((∏ w : InfinitePlace K, normAtPlace w x ^ χ.harmonicExponent w : ℝ) : ℂ)⁻¹ *
        (mixedEmbedding.norm x : ℂ) ^ (-s) := by
  have heq :
      ∫ y, (χ.archWeight y : ℂ) * archGaussian y x * (archNorm y : ℂ) ^ (s / 2) ∂archHaar K =
        ∫ y, archGaussian y x * (χ.archWeight y : ℂ) * (archNorm y : ℂ) ^ (s / 2) ∂archHaar K := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
    ring
  rw [heq, χ.integral_archGaussian_mul_archWeight_mul_archNorm_cpow x hs,
    prod_Gammaℝ_mult_mul_add_harmonicExponent]

end TauCeti.LFunctions.Grossencharacter
