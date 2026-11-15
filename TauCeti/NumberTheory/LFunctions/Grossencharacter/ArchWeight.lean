/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Archimedean
public import TauCeti.NumberTheory.LFunctions.Grossencharacter.HarmonicFactor
public import TauCeti.NumberTheory.LFunctions.Theta.GammaIntegral
import Mathlib.MeasureTheory.Integral.Pi
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# The archimedean weight and weighted gamma integral of a Grossencharacter

For a presented Grossencharacter `χ : Grossencharacter K 𝔪`, the twisted theta series carries the
harmonic polynomial `χ.harmonicFactor` of degree `P_w = χ.harmonicExponent w` at each infinite
place `w`. Under the unit action `unitScale u` on the archimedean parameters `y : realSpace K` and
radial scaling `surfaceScale x t`, the compensating archimedean weight of Neukirch VII (8.2)–(8.3)
is

`χ.archWeight y = ∏_w y_w ^ (P_w / 2)`.

Under `unitScale u`, `χ.archWeight` multiplies by `∏_w |u|_w ^ P_w` (`archWeight_unitScale`),
cancelling the inverse factor picked up when the twisted theta sum is reindexed by `u`. Under
`surfaceScale x t` (`0 ≤ t`), it scales by `t ^ (Tr(p) / (2 [K : ℚ]))`
(`archWeight_surfaceScale`), shifting the Mellin variable by `Tr(p) / [K : ℚ]`. Against the
factor `∏_w y_w ^ (-P_w)` of Hecke's lemma (`mixedFourier_harmonicFactor_mul_archGaussian`),
`χ.archWeight y` produces `χ.archWeight y⁻¹` (`archWeight_mul_prod_inv_pow`).

Integrating `(χ.archWeight y : ℂ) * archGaussian y x * (archNorm y : ℂ) ^ (s / 2)` against the
multiplicative Haar measure `archHaar K` for `mixedEmbedding.norm x ≠ 0` and
`∀ w, 0 < mult w * s.re + P_w` generalizes
`TauCeti.LFunctions.integral_archGaussian_mul_archNorm_cpow` to the product of shifted archimedean
gamma factors

`((2 : ℂ) ^ (s - 1)) ^ r₂ · 2 ^ ((∑_{w complex} P_w) / 2) · (∏_{w real} Γ_ℝ(s + P_w)) ·
  (∏_{w complex} Γ_ℂ(s + P_w / 2)) · (∏_w |x_w| ^ P_w)⁻¹ · |N(x)| ^ (-s)`

(`integral_archWeight_mul_archGaussian_mul_archNorm_cpow`), in which `(∏_w |x_w| ^ P_w)⁻¹` cancels
`‖χ.harmonicFactor x‖` and the shifted `Γ_ℝ` and `Γ_ℂ` factors match the archimedean gamma factor
of the unitary completion of `χ`.

## Main definitions

* `TauCeti.LFunctions.Grossencharacter.archWeight`: the parameter weight
  `∏_w y_w ^ (P_w / 2)` on `realSpace K`.

## Main results

* `TauCeti.LFunctions.Grossencharacter.archWeight_unitScale`: unit-scaling law under `unitScale`.
* `TauCeti.LFunctions.Grossencharacter.archWeight_surfaceScale`: radial-scaling law under
  `surfaceScale`.
* `TauCeti.LFunctions.Grossencharacter.archWeight_mul_prod_inv_pow`: absorption of the Hecke-lemma
  weight `∏_w y_w ^ (-P_w)` into `archWeight y⁻¹`.
* `TauCeti.LFunctions.Grossencharacter.prod_Gammaℝ_mult_mul_add_harmonicExponent`: decomposition of
  `∏_w Γ_ℝ(mult w · s + P_w)` into Deligne's `Γ_ℝ` and `Γ_ℂ` factors.
* `TauCeti.LFunctions.Grossencharacter.integrable_archWeight_mul_archGaussian_mul_archNorm_cpow`
  and `TauCeti.LFunctions.Grossencharacter.integral_archWeight_mul_archGaussian_mul_archNorm_cpow`:
  integrability and closed-form evaluation of the weighted archimedean gamma integral.

## References

* E. Hecke, *Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen
  (Zweite Mitteilung)*, Math. Z. **6** (1920), 11–51.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §§7–8.
-/

public section

noncomputable section

open Complex MeasureTheory NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Real

namespace TauCeti.LFunctions.Grossencharacter

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-! ### Definition and basic properties of `archWeight` -/

/-- **The archimedean parameter weight `N(y^(p/2))`** of Neukirch VII (8.2)–(8.3):
`∏_w y_w ^ (P_w / 2)` where `P_w = χ.harmonicExponent w`. -/
def archWeight (χ : Grossencharacter K 𝔪) (y : realSpace K) : ℝ :=
  ∏ w : InfinitePlace K, y w ^ ((χ.harmonicExponent w : ℝ) / 2)

/-- Defining product formula for `archWeight`. -/
theorem archWeight_apply (χ : Grossencharacter K 𝔪) (y : realSpace K) :
    χ.archWeight y = ∏ w : InfinitePlace K, y w ^ ((χ.harmonicExponent w : ℝ) / 2) :=
  (rfl)

@[simp]
theorem archWeight_one (χ : Grossencharacter K 𝔪) : χ.archWeight 1 = 1 := by
  simp [archWeight_apply]

/-- When `harmonicDegree` vanishes, `archWeight` is identically `1`. -/
theorem archWeight_of_harmonicDegree_eq_zero {χ : Grossencharacter K 𝔪}
    (h : χ.harmonicDegree = 0) (y : realSpace K) : χ.archWeight y = 1 := by
  have hw := χ.harmonicDegree_eq_zero_iff.mp h
  simp [archWeight_apply, hw]

/-- `archWeight` depends only on the presented Hecke character, not on the modulus. -/
theorem archWeight_congr {𝔫 : Modulus K} {χ : Grossencharacter K 𝔪} {ψ : Grossencharacter K 𝔫}
    (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) (y : realSpace K) :
    χ.archWeight y = ψ.archWeight y := by
  simp [archWeight_apply, harmonicExponent_congr h]

/-- Inverting a presentation preserves `archWeight`. -/
@[simp]
theorem archWeight_inverse (χ : Grossencharacter K 𝔪) (y : realSpace K) :
    χ.inverse.archWeight y = χ.archWeight y := by
  simp [archWeight_apply]

/-- A ray-class presentation with trivial archimedean modulus has constant weight `1`. -/
theorem archWeight_ofRayClassCharacter_of_infinitePart_eq_empty (h𝔪 : 𝔪.infinitePart = ∅)
    (η : RayClassCharacter 𝔪) (y : realSpace K) :
    (ofRayClassCharacter η).archWeight y = 1 :=
  archWeight_of_harmonicDegree_eq_zero
    (harmonicDegree_ofRayClassCharacter_of_infinitePart_eq_empty h𝔪 η) y

@[simp]
theorem archWeight_ofRayClassCharacter_one (η : RayClassCharacter (Modulus.one K))
    (y : realSpace K) : (ofRayClassCharacter η).archWeight y = 1 :=
  archWeight_of_harmonicDegree_eq_zero (harmonicDegree_ofRayClassCharacter_one η) y

/-- Any presentation of the trivial Hecke character has `archWeight` identically `1`. -/
theorem archWeight_of_toHeckeCharacter_eq_one {χ : Grossencharacter K 𝔪}
    (hχ : χ.toHeckeCharacter = 1) (y : realSpace K) : χ.archWeight y = 1 :=
  archWeight_of_harmonicDegree_eq_zero (harmonicDegree_of_toHeckeCharacter_eq_one hχ) y

/-- On nonnegative parameters, `archWeight y` is `∏_w √(y_w) ^ P_w`. -/
theorem archWeight_eq_prod_sqrt_pow (χ : Grossencharacter K 𝔪) {y : realSpace K}
    (hy : ∀ w, 0 ≤ y w) :
    χ.archWeight y = ∏ w : InfinitePlace K, √(y w) ^ χ.harmonicExponent w := by
  rw [archWeight_apply]
  exact Finset.prod_congr rfl fun w _ ↦ (Real.pow_sqrt_eq_rpow (hy w) _).symm

/-- `archWeight` is nonnegative on the nonnegative orthant. -/
theorem archWeight_nonneg (χ : Grossencharacter K 𝔪) {y : realSpace K} (hy : ∀ w, 0 ≤ y w) :
    0 ≤ χ.archWeight y :=
  Finset.prod_nonneg fun w _ ↦ Real.rpow_nonneg (hy w) _

/-- `archWeight` is strictly positive on the positive orthant. -/
theorem archWeight_pos (χ : Grossencharacter K 𝔪) {y : realSpace K} (hy : ∀ w, 0 < y w) :
    0 < χ.archWeight y :=
  Finset.prod_pos fun w _ ↦ Real.rpow_pos_of_pos (hy w) _

@[fun_prop]
theorem continuous_archWeight (χ : Grossencharacter K 𝔪) : Continuous χ.archWeight := by
  unfold archWeight
  exact continuous_finsetProd _ fun w _ ↦ (continuous_apply w).rpow_const fun _ ↦
    Or.inr (by positivity)

@[fun_prop]
theorem measurable_archWeight (χ : Grossencharacter K 𝔪) : Measurable χ.archWeight :=
  χ.continuous_archWeight.measurable

/-! ### Multiplicative, unit, and radial scaling laws -/

/-- `archWeight` splits across multiplication whenever the left factor is coordinatewise
nonnegative. -/
theorem archWeight_mul (χ : Grossencharacter K 𝔪) {x : realSpace K} (hx : ∀ w, 0 ≤ x w)
    (y : realSpace K) :
    χ.archWeight (x * y) = χ.archWeight x * χ.archWeight y := by
  simp only [archWeight_apply, Pi.mul_apply, Real.mul_rpow_of_nonneg_left (hx _),
    Finset.prod_mul_distrib]

/-- On coordinatewise nonnegative parameters, `archWeight` commutes with coordinatewise
inversion. -/
theorem archWeight_inv (χ : Grossencharacter K 𝔪) {y : realSpace K} (hy : ∀ w, 0 ≤ y w) :
    χ.archWeight y⁻¹ = (χ.archWeight y)⁻¹ := by
  rw [archWeight_apply, archWeight_apply, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun w _ ↦ Real.inv_rpow (hy w) _

/-- Multiplying `archWeight y` by the Hecke-lemma factor `∏_w y_w ^ (-P_w)` gives
`archWeight y⁻¹` (Neukirch VII (8.5)). -/
theorem archWeight_mul_prod_inv_pow (χ : Grossencharacter K 𝔪) {y : realSpace K}
    (hy : ∀ w, 0 < y w) :
    χ.archWeight y * (∏ w : InfinitePlace K, (y w)⁻¹ ^ χ.harmonicExponent w) =
      χ.archWeight y⁻¹ := by
  rw [archWeight_apply, archWeight_apply, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  have h1 : (y w)⁻¹ ^ χ.harmonicExponent w =
      ((y w)⁻¹ ^ ((χ.harmonicExponent w : ℝ) / 2)) ^ 2 := by
    rw [Real.rpow_div_two_sq (inv_nonneg.mpr (hy w).le), Real.rpow_natCast]
  have h2 :
      y w ^ ((χ.harmonicExponent w : ℝ) / 2) *
        (y w)⁻¹ ^ ((χ.harmonicExponent w : ℝ) / 2) = 1 := by
    rw [← Real.mul_rpow (hy w).le (inv_nonneg.mpr (hy w).le), mul_inv_cancel₀ (hy w).ne',
      Real.one_rpow]
  rw [Pi.inv_apply, h1, sq, ← mul_assoc, h2, one_mul]

/-- **Unit scaling of `archWeight`** (Neukirch VII (8.2)): `unitScale u` multiplies `archWeight`
by `∏_w |u|_w ^ P_w`. -/
theorem archWeight_unitScale (χ : Grossencharacter K 𝔪) (u : (𝓞 K)ˣ) (y : realSpace K) :
    χ.archWeight (unitScale u y) =
      (∏ w : InfinitePlace K, w (u : K) ^ χ.harmonicExponent w) * χ.archWeight y := by
  rw [archWeight_apply, archWeight_apply, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [unitScale_apply, Real.mul_rpow_of_nonneg_left (sq_nonneg _),
    Real.sq_rpow_div_two (apply_nonneg w _), Real.rpow_natCast]

/-- **Radial scaling of `archWeight`** (Neukirch VII (8.3)): for `0 ≤ t`, scaling by
`surfaceScale x t` multiplies `archWeight x` by `t ^ (Tr(p) / (2 [K : ℚ]))`. -/
theorem archWeight_surfaceScale (χ : Grossencharacter K 𝔪) (x : realSpace K) {t : ℝ}
    (ht : 0 ≤ t) :
    χ.archWeight (surfaceScale x t) =
      χ.archWeight x * t ^ ((χ.harmonicDegree : ℝ) / (2 * Module.finrank ℚ K)) := by
  have hsplit : χ.archWeight (surfaceScale x t) =
      χ.archWeight x *
        ∏ w : InfinitePlace K, t ^ ((χ.harmonicExponent w : ℝ) / (2 * Module.finrank ℚ K)) := by
    rw [archWeight_apply, archWeight_apply, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [surfaceScale_apply, mul_comm (x w), Real.mul_rpow_of_nonneg_left (Real.rpow_nonneg ht _),
      mul_comm, ← Real.rpow_mul ht]
    congr 2
    ring
  rw [hsplit]
  congr 1
  rcases ht.eq_or_lt with rfl | ht
  · by_cases hdeg : χ.harmonicDegree = 0
    · have hw := χ.harmonicDegree_eq_zero_iff.mp hdeg
      simp [hdeg, hw]
    · have hfin : 0 < Module.finrank ℚ K := Module.finrank_pos
      have hden : (0 : ℝ) < 2 * Module.finrank ℚ K := by positivity
      obtain ⟨w, hw⟩ : ∃ w, χ.harmonicExponent w ≠ 0 := by
        contrapose! hdeg
        exact χ.harmonicDegree_eq_zero_iff.mpr hdeg
      have hw' : ((χ.harmonicExponent w : ℝ) / (2 * Module.finrank ℚ K)) ≠ 0 :=
        (div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hw)) hden).ne'
      have hdeg' : ((χ.harmonicDegree : ℝ) / (2 * Module.finrank ℚ K)) ≠ 0 :=
        (div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hdeg)) hden).ne'
      rw [Finset.prod_eq_zero (Finset.mem_univ w) (Real.zero_rpow hw'), Real.zero_rpow hdeg']
  · rw [← Real.rpow_sum_of_pos ht, ← Finset.sum_div, ← Nat.cast_sum, ← harmonicDegree_def]

/-! ### The weighted archimedean gamma integral -/

/-- When `0 < s.re`, the shifted real part `(mult w : ℝ) * s.re + P_w` is positive at every
infinite place `w`. -/
theorem mul_re_add_harmonicExponent_pos (χ : Grossencharacter K 𝔪) {s : ℂ} (hs : 0 < s.re)
    (w : InfinitePlace K) :
    0 < (mult w : ℝ) * s.re + χ.harmonicExponent w := by
  have hm : (0 : ℝ) < mult w := Nat.cast_pos.mpr (Nat.pos_of_ne_zero mult_ne_zero)
  positivity

private theorem archWeight_mul_archGaussian_mul_archNorm_cpow_eq_prod (χ : Grossencharacter K 𝔪)
    {y : realSpace K} (hy : ∀ w, 0 < y w) (x : mixedSpace K) (s : ℂ) :
    (χ.archWeight y : ℂ) * archGaussian y x * (archNorm y : ℂ) ^ (s / 2) =
      ∏ w : InfinitePlace K,
        (y w : ℂ) ^ (((mult w : ℂ) * s + χ.harmonicExponent w) / 2) *
          (Real.exp (-(π * normAtPlace w x ^ 2 * y w)) : ℂ) := by
  have hw : (χ.archWeight y : ℂ) =
      ∏ w : InfinitePlace K, (y w : ℂ) ^ ((χ.harmonicExponent w : ℂ) / 2) := by
    rw [archWeight_apply, ofReal_prod]
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [ofReal_cpow (hy w).le]
    push_cast
    rfl
  have hn : (archNorm y : ℂ) ^ (s / 2) =
      ∏ w : InfinitePlace K, (y w : ℂ) ^ ((mult w : ℂ) * (s / 2)) := by
    rw [archNorm_apply, ofReal_prod_pow_mult_cpow fun w ↦ (hy w).le]
  have hg : archGaussian y x =
      ∏ w : InfinitePlace K, (Real.exp (-(π * normAtPlace w x ^ 2 * y w)) : ℂ) := by
    rw [archGaussian_apply, Finset.mul_sum, Real.exp_sum, ofReal_prod]
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    congr 2
    ring
  rw [hw, hg, hn, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [mul_right_comm, ← cpow_add _ _ (ofReal_ne_zero.mpr (hy w).ne')]
  congr 2
  ring

open scoped Classical in
/-- Decomposition of `∏_w Γ_ℝ(mult w · s + P_w)` into Deligne's `Γ_ℝ` and `Γ_ℂ` factors across the
real and complex infinite places of `K`. -/
theorem prod_Gammaℝ_mult_mul_add_harmonicExponent (χ : Grossencharacter K 𝔪) (s : ℂ) :
    (∏ w : InfinitePlace K, Gammaℝ ((mult w : ℂ) * s + χ.harmonicExponent w)) =
      ((2 : ℂ) ^ (s - 1)) ^ nrComplexPlaces K *
        (2 : ℂ) ^
          ((∑ w : {w : InfinitePlace K // w.IsComplex}, (χ.harmonicExponent w.1 : ℂ)) / 2) *
        ((∏ w : {w : InfinitePlace K // w.IsReal}, Gammaℝ (s + χ.harmonicExponent w.1)) *
          ∏ w : {w : InfinitePlace K // w.IsComplex},
            Gammaℂ (s + (χ.harmonicExponent w.1 : ℂ) / 2)) := by
  have hreal :
      (∏ w : {w : InfinitePlace K // w.IsReal},
        Gammaℝ ((mult w.1 : ℂ) * s + χ.harmonicExponent w.1)) =
      ∏ w : {w : InfinitePlace K // w.IsReal}, Gammaℝ (s + χ.harmonicExponent w.1) := by
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [mult_isReal w, Nat.cast_one, one_mul]
  have hcomplex :
      (∏ w : {w : InfinitePlace K // w.IsComplex},
        Gammaℝ ((mult w.1 : ℂ) * s + χ.harmonicExponent w.1)) =
      ((2 : ℂ) ^ (s - 1)) ^ nrComplexPlaces K *
        (2 : ℂ) ^
          ((∑ w : {w : InfinitePlace K // w.IsComplex}, (χ.harmonicExponent w.1 : ℂ)) / 2) *
        ∏ w : {w : InfinitePlace K // w.IsComplex},
          Gammaℂ (s + (χ.harmonicExponent w.1 : ℂ) / 2) := by
    have hstep (w : {w : InfinitePlace K // w.IsComplex}) :
        Gammaℝ ((mult w.1 : ℂ) * s + χ.harmonicExponent w.1) =
          (2 : ℂ) ^ (s - 1) * (2 : ℂ) ^ ((χ.harmonicExponent w.1 : ℂ) / 2) *
            Gammaℂ (s + (χ.harmonicExponent w.1 : ℂ) / 2) := by
      have harg : (mult w.1 : ℂ) * s + χ.harmonicExponent w.1 =
          2 * (s + (χ.harmonicExponent w.1 : ℂ) / 2) := by
        rw [mult_isComplex w, Nat.cast_ofNat]
        ring
      have hexp : s + (χ.harmonicExponent w.1 : ℂ) / 2 - 1 =
          (s - 1) + (χ.harmonicExponent w.1 : ℂ) / 2 := by ring
      rw [harg, Gammaℝ_two_mul, hexp, cpow_add _ _ two_ne_zero]
    simp_rw [hstep, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      ← TauCeti.cpow_sum two_ne_zero, ← Finset.sum_div]
  rw [prod_eq_prod_mul_prod, hreal, hcomplex]
  ring

/-- For `x` of nonzero norm and `s` with `0 < mult w * s.re + P_w` at every infinite place `w`,
the weighted archimedean Gaussian `(χ.archWeight y : ℂ) * archGaussian y x * N(y)^(s/2)` is
integrable against `archHaar K`. -/
theorem integrable_archWeight_mul_archGaussian_mul_archNorm_cpow {χ : Grossencharacter K 𝔪}
    {x : mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) {s : ℂ}
    (hs : ∀ w, 0 < (mult w : ℝ) * s.re + χ.harmonicExponent w) :
    Integrable (fun y ↦ (χ.archWeight y : ℂ) * archGaussian y x * (archNorm y : ℂ) ^ (s / 2))
      (archHaar K) := by
  have ha := normAtPlace_pos_of_norm_ne_zero hx
  have hz (w : InfinitePlace K) : 0 < ((mult w : ℂ) * s + χ.harmonicExponent w).re := by
    simpa using hs w
  have hint := Integrable.fintype_prod (μ := fun _ : InfinitePlace K ↦ multHaar)
    fun w ↦ integrable_cpow_div_two_mul_exp_neg_multHaar (ha w) (hz w)
  rw [← archHaar_def] at hint
  refine hint.congr ?_
  filter_upwards [ae_archHaar_pos] with y hy
  exact (χ.archWeight_mul_archGaussian_mul_archNorm_cpow_eq_prod hy x s).symm

/-- **The weighted archimedean gamma integral** in `Γ_ℝ`-product form: for `x` of nonzero norm and
`∀ w, 0 < mult w * s.re + P_w`,
`∫ N(y^(p/2)) exp(-π ∑_w y_w |x_w|²) N(y)^(s/2) dy/y =
  (∏_w Γ_ℝ(mult w · s + P_w)) · (∏_w |x_w| ^ P_w)⁻¹ · |N(x)| ^ (-s)`. -/
theorem integral_archWeight_mul_archGaussian_mul_archNorm_cpow_eq_prod_Gammaℝ
    {χ : Grossencharacter K 𝔪} {x : mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) {s : ℂ}
    (hs : ∀ w, 0 < (mult w : ℝ) * s.re + χ.harmonicExponent w) :
    ∫ y, (χ.archWeight y : ℂ) * archGaussian y x * (archNorm y : ℂ) ^ (s / 2) ∂archHaar K =
      (∏ w : InfinitePlace K, Gammaℝ ((mult w : ℂ) * s + χ.harmonicExponent w)) *
        ((∏ w : InfinitePlace K, normAtPlace w x ^ χ.harmonicExponent w : ℝ) : ℂ)⁻¹ *
        (mixedEmbedding.norm x : ℂ) ^ (-s) := by
  have ha := normAtPlace_pos_of_norm_ne_zero hx
  have hz (w : InfinitePlace K) : 0 < ((mult w : ℂ) * s + χ.harmonicExponent w).re := by
    simpa using hs w
  have hnorm_s : (mixedEmbedding.norm x : ℂ) ^ (-s) =
      ∏ w : InfinitePlace K, (normAtPlace w x : ℂ) ^ ((mult w : ℂ) * (-s)) := by
    rw [mixedEmbedding.norm_apply, ofReal_prod_pow_mult_cpow fun w ↦ (ha w).le]
  have hnorm_p :
      ((∏ w : InfinitePlace K, normAtPlace w x ^ χ.harmonicExponent w : ℝ) : ℂ)⁻¹ =
        ∏ w : InfinitePlace K, (normAtPlace w x : ℂ) ^ (-(χ.harmonicExponent w : ℂ)) := by
    rw [ofReal_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [ofReal_pow, cpow_neg, cpow_natCast]
  have hnorm_ps :
      (∏ w : InfinitePlace K,
        (normAtPlace w x : ℂ) ^ (-((mult w : ℂ) * s + χ.harmonicExponent w))) =
        ((∏ w : InfinitePlace K, normAtPlace w x ^ χ.harmonicExponent w : ℝ) : ℂ)⁻¹ *
          (mixedEmbedding.norm x : ℂ) ^ (-s) := by
    rw [hnorm_p, hnorm_s, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [← cpow_add _ _ (ofReal_ne_zero.mpr (ha w).ne')]
    congr 1
    ring
  calc ∫ y, (χ.archWeight y : ℂ) * archGaussian y x * (archNorm y : ℂ) ^ (s / 2) ∂archHaar K
      = ∫ y, ∏ w : InfinitePlace K,
          (y w : ℂ) ^ (((mult w : ℂ) * s + χ.harmonicExponent w) / 2) *
            (Real.exp (-(π * normAtPlace w x ^ 2 * y w)) : ℂ) ∂archHaar K := by
        refine integral_congr_ae ?_
        filter_upwards [ae_archHaar_pos] with y hy
        exact χ.archWeight_mul_archGaussian_mul_archNorm_cpow_eq_prod hy x s
    _ = ∏ w : InfinitePlace K,
          ∫ t, (t : ℂ) ^ (((mult w : ℂ) * s + χ.harmonicExponent w) / 2) *
            (Real.exp (-(π * normAtPlace w x ^ 2 * t)) : ℂ) ∂multHaar := by
        rw [archHaar_def]
        exact integral_fintype_prod_eq_prod (fun w (t : ℝ) ↦
          (t : ℂ) ^ (((mult w : ℂ) * s + χ.harmonicExponent w) / 2) *
            (Real.exp (-(π * normAtPlace w x ^ 2 * t)) : ℂ))
    _ = ∏ w : InfinitePlace K,
          Gammaℝ ((mult w : ℂ) * s + χ.harmonicExponent w) *
            (normAtPlace w x : ℂ) ^ (-((mult w : ℂ) * s + χ.harmonicExponent w)) := by
        exact Finset.prod_congr rfl fun w _ ↦
          integral_cpow_div_two_mul_exp_neg_multHaar (ha w) (hz w)
    _ = _ := by
        rw [Finset.prod_mul_distrib, hnorm_ps, mul_assoc]

open scoped Classical in
/-- **The weighted archimedean gamma integral** of a Grossencharacter in Deligne `Γ_ℝ` and `Γ_ℂ`
form (Neukirch VII §8): for `x` of nonzero norm and `∀ w, 0 < mult w * s.re + P_w`,
integrating `(χ.archWeight y : ℂ) * archGaussian y x * (archNorm y : ℂ) ^ (s / 2)` over
`archHaar K` yields the shifted gamma product times `(∏_w |x_w| ^ P_w)⁻¹ |N(x)| ^ (-s)`. -/
theorem integral_archWeight_mul_archGaussian_mul_archNorm_cpow {χ : Grossencharacter K 𝔪}
    {x : mixedSpace K} (hx : mixedEmbedding.norm x ≠ 0) {s : ℂ}
    (hs : ∀ w, 0 < (mult w : ℝ) * s.re + χ.harmonicExponent w) :
    ∫ y, (χ.archWeight y : ℂ) * archGaussian y x * (archNorm y : ℂ) ^ (s / 2) ∂archHaar K =
      ((2 : ℂ) ^ (s - 1)) ^ nrComplexPlaces K *
        (2 : ℂ) ^
          ((∑ w : {w : InfinitePlace K // w.IsComplex}, (χ.harmonicExponent w.1 : ℂ)) / 2) *
        ((∏ w : {w : InfinitePlace K // w.IsReal}, Gammaℝ (s + χ.harmonicExponent w.1)) *
          ∏ w : {w : InfinitePlace K // w.IsComplex},
            Gammaℂ (s + (χ.harmonicExponent w.1 : ℂ) / 2)) *
        ((∏ w : InfinitePlace K, normAtPlace w x ^ χ.harmonicExponent w : ℝ) : ℂ)⁻¹ *
        (mixedEmbedding.norm x : ℂ) ^ (-s) := by
  rw [integral_archWeight_mul_archGaussian_mul_archNorm_cpow_eq_prod_Gammaℝ hx hs,
    prod_Gammaℝ_mult_mul_add_harmonicExponent]

end TauCeti.LFunctions.Grossencharacter
