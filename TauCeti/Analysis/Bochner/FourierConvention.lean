/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Bochner.CharFunPositiveDefinite
public import TauCeti.Analysis.PositiveDefinite.Pullback

/-!
# Fourier-convention bridge for measures

Mathlib's Fourier transform uses the character `x ↦ exp (2π i x)`, while Mathlib's
characteristic function of a measure is `t ↦ ∫ q, exp (i ⟪q, t⟫) ∂μ q`. Bochner-type
statements are often written in the Fourier-transform convention

`a ↦ ∫ q, exp (-2π i ⟪a, q⟫) ∂μ q`.

This file records the exact conversion from Mathlib's Fourier integral to
`MeasureTheory.charFun`: at frequency `a`, it is `charFun μ (-(2π) • a)`. Combining this with the
existing finite-measure characteristic-function bridge gives the forward direction in the roadmap's
Fourier convention.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, the API bullet asking for
"a stated Fourier-convention conversion lemma between Mathlib's `2π` form
(`e^{-2πi⟨·,·⟩}`) and the characteristic-function form (`e^{i⟨·,·⟩}`)". No Mathlib code is
vendored; the conversion follows Mathlib's characteristic-function and Fourier-character
normalizations.

## Main declarations

* `TauCeti.MeasureTheory.fourierIntegral_one_eq_charFun`: conversion from Mathlib's
  Fourier integral of the constant function `1` to Mathlib's `charFun`.
* `TauCeti.MeasureTheory.fourierIntegral_one_isPositiveDefinite_of_star_eq_neg`: the finite-measure
  positive-definiteness consequence for this Fourier integral.
* `TauCeti.MeasureTheory.continuous_fourierIntegral_one`: continuity for the same finite-measure
  Fourier integral.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 4.
-/

public section

open MeasureTheory RealInnerProductSpace Complex

namespace TauCeti

namespace MeasureTheory

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] {μ : Measure E}

/-- Pointwise integral expression for Mathlib's Fourier integral of the constant function `1` in
the `e^{-2πi⟪a,q⟫}` convention. -/
theorem fourierIntegral_one_apply (a : E) :
    VectorFourier.fourierIntegral Real.fourierChar μ (innerₗ E) (1 : E → ℂ) a =
      ∫ q, exp (-2 * Real.pi * I * (⟪a, q⟫ : ℂ)) ∂μ := by
  rw [Real.vector_fourierIntegral_eq_integral_exp_smul]
  congr with q
  simp only [innerₗ_apply_apply, Pi.one_apply, smul_eq_mul, mul_one]
  congr 1
  rw [real_inner_comm]
  ring_nf
  simp [mul_assoc, mul_comm]

/-- Mathlib's `e^{-2πi⟪a,q⟫}` Fourier integral of the constant function `1` is the characteristic
function evaluated at `-(2π) • a`. This is the named conversion between Mathlib's Fourier
convention and Mathlib's `MeasureTheory.charFun` convention. -/
@[simp]
theorem fourierIntegral_one_eq_charFun (a : E) :
    VectorFourier.fourierIntegral Real.fourierChar μ (innerₗ E) (1 : E → ℂ) a =
      charFun μ (-(2 * Real.pi) • a) := by
  rw [charFun_eq_fourierIntegral']
  congr 1
  rw [smul_smul]
  have h : Real.pi⁻¹ * 2⁻¹ * (2 * Real.pi) = (1 : ℝ) := by
    field_simp [Real.pi_ne_zero]
  simp [h]

/-- Function-level form of `fourierIntegral_one_eq_charFun`. -/
theorem fourierIntegral_one_eq_charFun_fun :
    (fun a : E => VectorFourier.fourierIntegral Real.fourierChar μ (innerₗ E) (1 : E → ℂ) a) =
      fun a : E => charFun μ (-(2 * Real.pi) • a) := by
  ext a
  exact fourierIntegral_one_eq_charFun (μ := μ) a

/-- Mathlib's Fourier integral of the constant function `1` at zero is the measure's
`μ.real Set.univ` mass. -/
@[simp]
theorem fourierIntegral_one_zero :
    VectorFourier.fourierIntegral Real.fourierChar μ (innerₗ E) (1 : E → ℂ) 0 =
      μ.real Set.univ := by
  simp [fourierIntegral_one_eq_charFun (μ := μ)]

/-- Norm bound for Mathlib's Fourier integral of the constant function `1`, inherited from the
corresponding characteristic-function bound. -/
theorem norm_fourierIntegral_one_le (a : E) :
    ‖VectorFourier.fourierIntegral Real.fourierChar μ (innerₗ E) (1 : E → ℂ) a‖ ≤
      μ.real Set.univ := by
  simpa [fourierIntegral_one_eq_charFun (μ := μ) a] using
    norm_charFun_le (μ := μ) (-(2 * Real.pi) • a)

/-- Probability-measure specialization of `norm_fourierIntegral_one_le`. -/
theorem norm_fourierIntegral_one_le_one [IsProbabilityMeasure μ] (a : E) :
    ‖VectorFourier.fourierIntegral Real.fourierChar μ (innerₗ E) (1 : E → ℂ) a‖ ≤ 1 := by
  simpa [fourierIntegral_one_eq_charFun (μ := μ) a] using
    norm_charFun_le_one (μ := μ) (-(2 * Real.pi) • a)

variable [OpensMeasurableSpace E]
variable [IsFiniteMeasure μ]

/-- In the explicit negation-involution convention, Mathlib's Fourier integral of the constant
function `1` is positive definite. -/
theorem fourierIntegral_one_isPositiveDefinite_of_star_eq_neg [StarAddMonoid E]
    (hstar : ∀ x : E, star x = -x) :
    IsPositiveDefinite
      (fun a : E => VectorFourier.fourierIntegral Real.fourierChar μ (innerₗ E) (1 : E → ℂ) a) := by
  rw [fourierIntegral_one_eq_charFun_fun]
  exact (charFun_isPositiveDefinite_of_star_eq_neg (μ := μ) hstar).comp_addMonoidHom
    (DistribSMul.toAddMonoidHom E (-(2 * Real.pi))) (by
      intro x
      simp [hstar])

end Seminormed

section Normed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsFiniteMeasure μ]

/-- Mathlib's Fourier integral of the constant function `1` is continuous for finite measures. -/
theorem continuous_fourierIntegral_one :
    Continuous
      (fun a : E => VectorFourier.fourierIntegral Real.fourierChar μ (innerₗ E) (1 : E → ℂ) a) := by
  rw [fourierIntegral_one_eq_charFun_fun]
  exact MeasureTheory.continuous_charFun.comp (continuous_const.smul continuous_id)

/-- Mathlib's Fourier integral of the constant function `1` is continuous and positive definite
under an explicit negation involution. -/
theorem continuous_fourierIntegral_one_and_isPositiveDefinite_of_star_eq_neg [StarAddMonoid E]
    (hstar : ∀ x : E, star x = -x) :
    Continuous
        (fun a : E => VectorFourier.fourierIntegral Real.fourierChar μ (innerₗ E) (1 : E → ℂ) a) ∧
      IsPositiveDefinite
        (fun a : E => VectorFourier.fourierIntegral Real.fourierChar μ (innerₗ E) (1 : E → ℂ) a) :=
  ⟨continuous_fourierIntegral_one,
    fourierIntegral_one_isPositiveDefinite_of_star_eq_neg hstar⟩

end Normed

end MeasureTheory

end TauCeti
