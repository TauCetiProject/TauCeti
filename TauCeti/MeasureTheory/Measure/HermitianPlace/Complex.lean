/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TauCeti.MeasureTheory.Measure.HermitianPlace.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The complex numbers as a place

The field `ℂ` with complex conjugation is a place (`TauCeti.HermitianPlace.complex`), with

* `τ = 1/2` and `δ = i/2`;
* `ν` the image of Lebesgue measure under `t ↦ it`, so that `(a, b) ↦ τδ⁻¹a + b = -ia + b`
  carries `ν × ν` to Lebesgue measure on `ℂ`;
* the modulus `mod x = |x|²`: a complex matrix `M` scales Lebesgue measure of `ℂⁿ` by
  `|det M|²`, the real determinant of `M` (`TauCeti.map_mulVec_addHaar_eq_smul`);
* the character `ψ(x) = exp(x - conj x) = exp(2i Im x)` (`TauCeti.HermitianPlace.complexChar`);
* the Plancherel constant `c_ℂ = π²`, attained by the Gaussian `G(v) = exp(-|v|²)`, whose
  transform `w ↦ ∫ G(v) ψ(conj v * w) dv` is `π exp(-|w|²)`
  (`TauCeti.HermitianPlace.integral_gaussian_mul_complexChar`), of `L¹` norm `π²`;
* every nonzero complex number a unit, and `|u|⁻² = g(u)²` for the locally integrable
  `g(u) = |u|⁻¹`.

## Main definitions

* `TauCeti.HermitianPlace.complexChar`: the character `x ↦ exp(x - conj x)` of `ℂ`.
* `TauCeti.HermitianPlace.complex`: the place `ℂ`.

## Main results

* `TauCeti.HermitianPlace.integral_gaussian_mul_complexChar`,
  `TauCeti.HermitianPlace.lintegral_enorm_integral_gaussian_mul_complexChar`: the transform of
  the Gaussian under `ψ` and its `L¹` norm `π²`.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, thesis (1950), Chapter 2:
  the archimedean places, their characters and self-dual measures.

The data, and the Gaussian attaining `c_ℂ = π²`, are those of `New.Floors.complexPlace` in the Lean
project grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
PBC), file `src/Lib/DiscreteSeries/Bruhat/ComplexPlace.lean`.
-/

public section

open MeasureTheory Matrix Complex ComplexConjugate
open scoped ENNReal Real

namespace TauCeti.HermitianPlace

/-- The additive character `x ↦ exp(x - conj x) = exp(2i Im x)` of `ℂ`. -/
noncomputable def complexChar : AddChar ℂ Circle where
  toFun x := Circle.exp (2 * x.im)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by simp [mul_add, Circle.exp_add]

/-- `ψ(x) = exp(x - conj x)`. -/
theorem complexChar_apply (x : ℂ) : (complexChar x : ℂ) = Complex.exp (x - conj x) := by
  simp only [complexChar, AddChar.coe_mk, Circle.coe_exp, sub_conj]

/-- The character `x ↦ exp(x - conj x)` is continuous. -/
theorem continuous_complexChar : Continuous complexChar :=
  Circle.exp.continuous.comp (continuous_const.mul continuous_im)

/-- The modulus `x ↦ |x|²` of `ℂ`. -/
noncomputable def complexModulus : ℂ →* ℝ≥0∞ where
  toFun x := ‖x‖ₑ ^ 2
  map_one' := by simp
  map_mul' x y := by simp [mul_pow]

/-- `mod x = |x|²`. -/
@[simp]
theorem complexModulus_apply (x : ℂ) : complexModulus x = ‖x‖ₑ ^ 2 := (rfl)

/-- The imaginary axis `t ↦ it`, as an isomorphism of topological groups from `ℝ` onto the skew
elements of `ℂ`. -/
noncomputable def imaginaryAxisEquiv : ℝ ≃ₜ+ skewAdjoint ℂ where
  toFun t := ⟨t * I, by simp [skewAdjoint.mem_iff]⟩
  invFun z := (z : ℂ).im
  left_inv t := by simp
  right_inv z := by
    have h : (z : ℂ).re = 0 := by
      have := congrArg re (skewAdjoint.mem_iff.1 z.property)
      simp only [star_def, conj_re, neg_re] at this
      linarith
    ext : 1
    apply Complex.ext <;> simp [h]
  map_add' s t := by ext : 1; simp [add_mul]
  continuous_toFun := (continuous_ofReal.mul continuous_const).subtype_mk fun t ↦ by
    simp [skewAdjoint.mem_iff]
  continuous_invFun := continuous_im.comp continuous_subtypeVal

/-- The imaginary axis sends `t` to `it`. -/
@[simp]
theorem coe_imaginaryAxisEquiv (t : ℝ) : (imaginaryAxisEquiv t : ℂ) = t * I := by
  simp [imaginaryAxisEquiv]

/-- `(a, b) ↦ -ia + b` carries the product of two copies of the image of Lebesgue measure under
`t ↦ it` to Lebesgue measure on `ℂ`. -/
theorem map_prod_imaginaryAxisEquiv :
    (((volume : Measure ℝ).map imaginaryAxisEquiv).prod
      ((volume : Measure ℝ).map imaginaryAxisEquiv)).map
      (fun p : skewAdjoint ℂ × skewAdjoint ℂ ↦ -I * p.1 + p.2) = volume := by
  have he : Measurable imaginaryAxisEquiv := imaginaryAxisEquiv.continuous.measurable
  rw [Measure.map_prod_map _ _ he he, Measure.map_map (by fun_prop) (he.prodMap he),
    ← Measure.volume_eq_prod, ← volume_preserving_equiv_real_prod.symm.map_eq]
  congr 1
  ext p : 1
  apply Complex.ext <;> simp

/-- The Gaussian `exp(-|v|²)` is integrable on `ℂ`. -/
private theorem integrable_rexp_neg_norm_sq : Integrable fun v : ℂ ↦ Real.exp (-‖v‖ ^ 2) := by
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := 1) (by simp) 0 0
  refine h.norm.congr (Filter.Eventually.of_forall fun v ↦ ?_)
  simp [Complex.norm_exp, ← ofReal_pow]

/-- The transform `w ↦ ∫ G(v) ψ(conj v * w) dv` of the Gaussian `G(v) = exp(-|v|²)` under the
character `ψ(x) = exp(x - conj x)` is `π exp(-|w|²)`. -/
theorem integral_gaussian_mul_complexChar (w : ℂ) :
    ∫ v : ℂ, (Real.exp (-‖v‖ ^ 2) : ℂ) * complexChar (conj v * w) =
      π * Complex.exp (-‖w‖ ^ 2) := by
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := ℂ) (b := 1) (by simp)
    (2 * I) (-I * w)
  convert h using 1
  · refine integral_congr_ae (Filter.Eventually.of_forall fun v ↦ ?_)
    beta_reduce
    rw [complexChar_apply, ofReal_exp, ← Complex.exp_add]
    congr 1
    apply Complex.ext
    · simp [Complex.inner]
    · simp [Complex.inner]
      ring
  · rw [Complex.finrank_real_complex]
    simp only [div_one, Nat.cast_ofNat, div_self (two_ne_zero' ℂ), cpow_one, norm_mul,
      norm_neg, norm_I, one_mul]
    congr 2
    ring_nf
    simp [I_sq]

/-- The transform of the Gaussian under `ψ(x) = exp(x - conj x)` has `L¹` norm `π²`. -/
theorem lintegral_enorm_integral_gaussian_mul_complexChar :
    ∫⁻ w : ℂ, ‖∫ v : ℂ, (Real.exp (-‖v‖ ^ 2) : ℂ) * complexChar (conj v * w)‖ₑ =
      ENNReal.ofReal (π ^ 2) := by
  have h (w : ℂ) :
      ‖(π : ℂ) * Complex.exp (-‖w‖ ^ 2)‖ₑ = ENNReal.ofReal (π * Real.exp (-‖w‖ ^ 2)) := by
    rw [← ofReal_norm, norm_mul, Complex.norm_exp]
    simp [abs_of_pos Real.pi_pos, ← ofReal_pow]
  simp_rw [integral_gaussian_mul_complexChar, h]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_rexp_neg_norm_sq.const_mul π)
    (Filter.Eventually.of_forall fun w ↦ by positivity), integral_const_mul]
  have hg := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) (b := 1) one_pos
  simp only [neg_mul, one_mul, Complex.finrank_real_complex, div_one] at hg
  rw [hg]
  norm_num [sq]

/-- `u ↦ |u|⁻¹` is locally integrable on `ℂ`. -/
private theorem locallyIntegrable_norm_inv : LocallyIntegrable fun u : ℂ ↦ ‖u‖⁻¹ := by
  refine locallyIntegrable_of_norm_le_rpow (μ := volume) (C := 1) (α := 1)
    (by simp) (by simp) (Filter.Eventually.of_forall fun u ↦ ?_)
    (continuous_norm.measurable.inv).aestronglyMeasurable
  simp [Real.rpow_neg_one]

/-- The complex numbers with complex conjugation are a place, with `τ = 1/2`, `δ = i/2`, `ν` the
image of Lebesgue measure under `t ↦ it`, the modulus `mod x = |x|²`, the character
`ψ(x) = exp(x - conj x)` and the Plancherel constant `c_ℂ = π²`. -/
noncomputable def complex : HermitianPlace ℂ where
  τ := 2⁻¹
  τ_add_star := by simp [← two_mul]
  δ := Units.mk0 (I / 2) (by simp)
  star_δ := by simp [neg_div]
  ν := (volume : Measure ℝ).map imaginaryAxisEquiv
  isAddHaarMeasure_ν := ContinuousAddEquiv.isAddHaarMeasure_map _ _
  map_prod_ν := by
    convert map_prod_imaginaryAxisEquiv using 3 with p
    simp [div_eq_mul_inv, mul_comm]
  modulus := complexModulus
  measurable_modulus := measurable_eNorm.pow_const 2
  modulus_star x := by simp
  map_mulVec_fin _ M hM := by
    simpa [← ofReal_norm, ENNReal.ofReal_pow] using
      map_mulVec_addHaar_eq_smul (μ := volume) hM.ne_zero
  ψ := complexChar
  continuous_ψ := continuous_complexChar
  plancherelConst := ENNReal.ofReal (π ^ 2)
  exists_damping_kernel := ⟨fun v ↦ Real.exp (-‖v‖ ^ 2), by fun_prop, integrable_rexp_neg_norm_sq,
    fun _ ↦ (Real.exp_pos _).le, by simp,
    (lintegral_enorm_integral_gaussian_mul_complexChar).le⟩
  ae_isUnit := (Measure.ae_ne volume 0).mono fun _ hx ↦ isUnit_iff_ne_zero.2 hx
  exists_locallyIntegrable := ⟨fun u ↦ ‖u‖⁻¹, locallyIntegrable_norm_inv, fun u ↦ by
    simp [← ofReal_norm, ENNReal.ofReal_inv_of_pos (norm_pos_iff.2 u.ne_zero), ENNReal.inv_pow]⟩

@[simp] theorem complex_τ : complex.τ = 2⁻¹ := (rfl)
@[simp] theorem coe_complex_δ : (complex.δ : ℂ) = I / 2 := (rfl)
@[simp] theorem complex_ν : complex.ν = (volume : Measure ℝ).map imaginaryAxisEquiv := (rfl)
@[simp] theorem complex_modulus (x : ℂ) : complex.modulus x = ‖x‖ₑ ^ 2 := (rfl)
@[simp] theorem complex_ψ : complex.ψ = complexChar := (rfl)
@[simp] theorem complex_plancherelConst : complex.plancherelConst = ENNReal.ofReal (π ^ 2) := (rfl)

end TauCeti.HermitianPlace
