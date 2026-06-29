/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Bochner.CharFunPositiveDefinite
public import TauCeti.Analysis.PositiveDefinite.Pullback

/-!
# Fourier-convention bridge for finite measures

Mathlib's Fourier transform uses the character `x ↦ exp (2π i x)`, while Mathlib's
characteristic function of a finite measure is `t ↦ ∫ q, exp (i ⟪q, t⟫) ∂μ q`. Bochner-type
statements are often written in the Fourier-transform convention

`a ↦ ∫ q, exp (-2π i ⟪a, q⟫) ∂μ q`.

This file records the exact conversion from Mathlib's Fourier integral to
`MeasureTheory.charFun`: at frequency `a`, it is `charFun μ (-(2π) • a)`. Combining this with the
existing characteristic-function bridge gives the finite-measure forward direction in the roadmap's
Fourier convention.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, the API bullet asking for
"a stated Fourier-convention conversion lemma between Mathlib's `2π` form
(`e^{-2πi⟨·,·⟩}`) and the characteristic-function form (`e^{i⟨·,·⟩}`)". No Mathlib code is
vendored; the conversion follows Mathlib's characteristic-function and Fourier-character
normalizations.

## Main declarations

* `TauCeti.MeasureTheory.fourierStieltjesTransform`: Mathlib's Fourier integral of the constant
  function `1`, the finite-measure Fourier-Stieltjes transform.
* `TauCeti.MeasureTheory.fourierStieltjesTransform_eq_charFun`: conversion to Mathlib's `charFun`.
* `TauCeti.MeasureTheory.norm_fourierStieltjesTransform_le`: the finite-measure norm bound.
* `TauCeti.MeasureTheory.continuous_fourierStieltjesTransform`: continuity for finite measures.
* `TauCeti.MeasureTheory.fourierStieltjesTransform_isPositiveDefinite_of_star_eq_neg`: the
  finite-measure transform is positive definite for an explicit negation involution.

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
  [MeasurableSpace E] {μ : Measure E} [IsFiniteMeasure μ]

/-- The Fourier-Stieltjes transform of a finite measure in Mathlib's `e^{-2πi⟪a,q⟫}` Fourier
convention, phrased as Mathlib's Fourier integral of the constant function `1`. -/
noncomputable def fourierStieltjesTransform (μ : Measure E) [IsFiniteMeasure μ] (a : E) : ℂ :=
  VectorFourier.fourierIntegral Real.fourierChar μ (innerₗ E) 1 a

/-- The pointwise integral expression for `fourierStieltjesTransform`. -/
theorem fourierStieltjesTransform_apply (a : E) :
    fourierStieltjesTransform μ a = ∫ q, exp (-2 * Real.pi * I * (⟪a, q⟫ : ℂ)) ∂μ := by
  rw [fourierStieltjesTransform, VectorFourier.fourierIntegral]
  congr with q
  simp only [Real.fourierChar_apply', innerₗ_apply_apply, Circle.smul_def, Circle.coe_exp,
    Pi.ofNat_apply, smul_eq_mul, mul_one]
  congr 1
  rw [real_inner_comm]
  rw [ofReal_mul, ofReal_mul, ofReal_neg]
  ring_nf
  simp [mul_assoc, mul_left_comm, mul_comm]

/-- Mathlib's `e^{-2πi⟪a,q⟫}` Fourier integral is the characteristic function evaluated at
`-(2π) • a`. This is the named conversion between Mathlib's Fourier convention and Mathlib's
`MeasureTheory.charFun` convention. -/
theorem fourierStieltjesTransform_eq_charFun (a : E) :
    fourierStieltjesTransform μ a = charFun μ (-(2 * Real.pi) • a) := by
  rw [charFun_eq_fourierIntegral']
  congr 1
  rw [smul_smul]
  have h : Real.pi⁻¹ * 2⁻¹ * (2 * Real.pi) = (1 : ℝ) := by
    field_simp [Real.pi_ne_zero]
  simp [h]

/-- Function-level form of `fourierStieltjesTransform_eq_charFun`. -/
theorem fourierStieltjesTransform_eq_charFun_fun :
    fourierStieltjesTransform μ = fun a : E => charFun μ (-(2 * Real.pi) • a) := by
  ext a
  exact fourierStieltjesTransform_eq_charFun (μ := μ) a

/-- The Fourier-Stieltjes transform at the origin is the total mass, as a complex number. -/
@[simp]
theorem fourierStieltjesTransform_zero :
    fourierStieltjesTransform μ 0 = μ.real Set.univ := by
  rw [fourierStieltjesTransform_eq_charFun]
  simp

/-- The Fourier-Stieltjes transform of the zero measure is zero. -/
@[simp]
theorem fourierStieltjesTransform_zero_measure (a : E) :
    fourierStieltjesTransform (0 : Measure E) a = 0 := by
  rw [fourierStieltjesTransform_eq_charFun]
  simp

/-- The Fourier-Stieltjes transform of a finite measure is bounded by the total mass. -/
theorem norm_fourierStieltjesTransform_le (a : E) :
    ‖fourierStieltjesTransform μ a‖ ≤ μ.real Set.univ := by
  rw [fourierStieltjesTransform_eq_charFun]
  exact norm_charFun_le (μ := μ) (-(2 * Real.pi) • a)

/-- The Fourier-Stieltjes transform of a probability measure has norm at most one. -/
theorem norm_fourierStieltjesTransform_le_one [IsProbabilityMeasure μ] (a : E) :
    ‖fourierStieltjesTransform μ a‖ ≤ 1 :=
  (norm_fourierStieltjesTransform_le (μ := μ) a).trans_eq (by simp)

variable [OpensMeasurableSpace E]

/-- In the explicit negation-involution convention, the Fourier-Stieltjes transform of a finite
measure is positive definite. -/
theorem fourierStieltjesTransform_isPositiveDefinite_of_star_eq_neg [StarAddMonoid E]
    (hstar : ∀ x : E, star x = -x) :
    IsPositiveDefinite (fourierStieltjesTransform μ) := by
  rw [fourierStieltjesTransform_eq_charFun_fun]
  exact (charFun_isPositiveDefinite_of_star_eq_neg (μ := μ) hstar).comp_addMonoidHom
    (DistribSMul.toAddMonoidHom E (-(2 * Real.pi))) (by
      intro x
      simp [hstar])

end Seminormed

section Normed

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsFiniteMeasure μ]

/-- The Fourier-Stieltjes transform of a finite measure is continuous. -/
theorem continuous_fourierStieltjesTransform : Continuous (fourierStieltjesTransform μ) := by
  rw [fourierStieltjesTransform_eq_charFun_fun]
  exact MeasureTheory.continuous_charFun.comp (continuous_const.smul continuous_id)

/-- The Fourier-Stieltjes transform of a finite measure is continuous and positive definite under an
explicit negation involution. -/
theorem continuous_fourierStieltjesTransform_and_isPositiveDefinite_of_star_eq_neg [StarAddMonoid E]
    [OpensMeasurableSpace E] (hstar : ∀ x : E, star x = -x) :
    Continuous (fourierStieltjesTransform μ) ∧ IsPositiveDefinite (fourierStieltjesTransform μ) :=
  ⟨continuous_fourierStieltjesTransform,
    fourierStieltjesTransform_isPositiveDefinite_of_star_eq_neg hstar⟩

end Normed

end MeasureTheory

end TauCeti
