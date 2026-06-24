/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Bochner.CharFunPositiveDefinite
public import TauCeti.Analysis.PositiveDefinite.Pullback
public import Mathlib.Analysis.Fourier.FourierTransform

/-!
# The Fourier-transform convention for finite measures

Mathlib's characteristic function of a finite measure is
`MeasureTheory.charFun μ t = ∫ x, exp (⟪x, t⟫ * I) ∂μ`, while Mathlib's Fourier transform on a
real inner-product space uses the phase `exp (-2π i ⟪a, x⟫)`. This file packages the finite-measure
Fourier transform in that second convention and records the scaling conversion to `charFun`.

This is the Fourier-convention bridge requested in Part C of the `OneParameterSemigroups`
roadmap, before the Bochner representation theorem: downstream statements can be phrased in the
usual Mathlib Fourier convention and still reuse the characteristic-function uniqueness,
continuity, and positive-definiteness API.

## Main declarations

* `TauCeti.fourierCharFun`: the finite-measure transform
  `a ↦ ∫ q, exp (-2π i ⟪a, q⟫) ∂μ`.
* `TauCeti.fourierCharFun_eq_charFun_neg_two_pi_smul`: the conversion to
  `MeasureTheory.charFun μ (-(2π) • a)`.
* `TauCeti.norm_fourierCharFun_le`: the standard total-mass bound for the transform.
* `TauCeti.continuous_fourierCharFun`: continuity for finite measures on second-countable real
  inner-product spaces.
* `TauCeti.fourierCharFun_isPositiveDefinite_of_star_eq_neg`: positive-definiteness under the
  negation involution.

The convention follows Mathlib's `Real.fourier_eq'` and `MeasureTheory.charFun_apply`; no formal
code is vendored.
-/

public section

open MeasureTheory

namespace TauCeti

open scoped ComplexOrder
open scoped InnerProductSpace

section Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  (μ : Measure E)

/-- The finite-measure Fourier transform in Mathlib's `2π` convention:
`a ↦ ∫ q, exp (-2π i ⟪a, q⟫) ∂μ`. -/
@[expose]
noncomputable def fourierCharFun (μ : Measure E) (a : E) : ℂ :=
  ∫ q, Complex.exp (-2 * Real.pi * Complex.I * (⟪a, q⟫_ℝ : ℂ)) ∂μ

/-- The defining integral for `fourierCharFun`. -/
theorem fourierCharFun_apply (a : E) :
    fourierCharFun μ a =
      ∫ q, Complex.exp (-2 * Real.pi * Complex.I * (⟪a, q⟫_ℝ : ℂ)) ∂μ :=
  rfl

/-- The Mathlib-Fourier finite-measure transform is the characteristic function evaluated at the
scaled frequency `-(2π) • a`. This is the basic conversion between the `e^{i⟪x,t⟫}` probability
convention and the `e^{-2πi⟪a,x⟫}` Fourier convention. -/
theorem fourierCharFun_eq_charFun_neg_two_pi_smul (a : E) :
    fourierCharFun μ a = MeasureTheory.charFun μ (-(2 * Real.pi) • a) := by
  rw [fourierCharFun_apply, MeasureTheory.charFun_apply]
  congr with q
  have hinner : ⟪q, (-(2 * Real.pi)) • a⟫_ℝ = -(2 * Real.pi) * ⟪a, q⟫_ℝ := by
    rw [inner_smul_right, real_inner_comm]
  rw [hinner]
  push_cast
  ring_nf

/-- The conversion lemma as a function equality. -/
theorem fourierCharFun_eq_charFun_comp_neg_two_pi_smul :
    fourierCharFun μ = fun a : E => MeasureTheory.charFun μ (-(2 * Real.pi) • a) := by
  funext a
  exact fourierCharFun_eq_charFun_neg_two_pi_smul μ a

/-- The Fourier-convention transform is bounded by the total mass of the finite measure. -/
theorem norm_fourierCharFun_le (a : E) : ‖fourierCharFun μ a‖ ≤ μ.real Set.univ := by
  rw [fourierCharFun_eq_charFun_neg_two_pi_smul]
  exact MeasureTheory.norm_charFun_le (μ := μ) _

/-- For a probability measure, the Fourier-convention transform is bounded by `1`. -/
theorem norm_fourierCharFun_le_one [IsProbabilityMeasure μ] (a : E) :
    ‖fourierCharFun μ a‖ ≤ 1 := by
  rw [fourierCharFun_eq_charFun_neg_two_pi_smul]
  exact MeasureTheory.norm_charFun_le_one (μ := μ) _

/-- The value at zero is the total real mass of the finite measure. -/
@[simp]
theorem fourierCharFun_zero : fourierCharFun μ (0 : E) = μ.real Set.univ := by
  rw [fourierCharFun_eq_charFun_neg_two_pi_smul]
  simp

end Basic

section Continuity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] {μ : Measure E} [IsFiniteMeasure μ]

/-- The finite-measure Fourier transform is continuous in Mathlib's `2π` convention. -/
theorem continuous_fourierCharFun : Continuous (fourierCharFun μ : E → ℂ) := by
  rw [fourierCharFun_eq_charFun_comp_neg_two_pi_smul]
  exact MeasureTheory.continuous_charFun.comp (continuous_const_smul (-(2 * Real.pi)))

/-- The finite-measure Fourier transform is continuous at every point. -/
theorem continuousAt_fourierCharFun (a : E) : ContinuousAt (fourierCharFun μ : E → ℂ) a :=
  continuous_fourierCharFun.continuousAt

end Continuity

section PositiveDefinite

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [StarAddMonoid E]

/-- The scaling map `a ↦ -(2π) • a` preserves the negation involution. -/
theorem neg_two_pi_smul_star_of_star_eq_neg (hstar : ∀ a : E, star a = -a) (a : E) :
    (-(2 * Real.pi)) • star a = star ((-(2 * Real.pi)) • a) := by
  simp [hstar]

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasure μ]

/-- In Mathlib's Fourier convention, the transform of a finite measure is positive definite under
the negation involution. -/
lemma fourierCharFun_isPositiveDefinite_of_star_eq_neg (hstar : ∀ a : E, star a = -a) :
    IsPositiveDefinite (fourierCharFun μ : E → ℂ) := by
  rw [fourierCharFun_eq_charFun_comp_neg_two_pi_smul]
  exact (charFun_isPositiveDefinite_of_star_eq_neg (μ := μ) hstar).comp_addMonoidHom
    (DistribSMul.toAddMonoidHom E (-(2 * Real.pi)))
    (neg_two_pi_smul_star_of_star_eq_neg hstar)

variable [SecondCountableTopology E]

/-- In Mathlib's Fourier convention, the transform of a finite measure is both continuous and
positive definite under the negation involution. -/
theorem continuous_fourierCharFun_and_isPositiveDefinite_of_star_eq_neg
    (hstar : ∀ a : E, star a = -a) :
    Continuous (fourierCharFun μ : E → ℂ) ∧ IsPositiveDefinite (fourierCharFun μ : E → ℂ) :=
  ⟨continuous_fourierCharFun, fourierCharFun_isPositiveDefinite_of_star_eq_neg hstar⟩

end PositiveDefinite

end TauCeti
