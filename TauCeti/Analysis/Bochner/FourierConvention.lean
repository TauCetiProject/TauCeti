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

This file gives that convention a local Tau Ceti name and records the exact conversion to
`MeasureTheory.charFun`: it is `charFun μ (-(2π) • a)`. Combining this with the existing
characteristic-function bridge gives the finite-measure forward direction in the roadmap's
Fourier convention.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, the API bullet asking for
"a stated Fourier-convention conversion lemma between Mathlib's `2π` form
(`e^{-2πi⟨·,·⟩}`) and the characteristic-function form (`e^{i⟨·,·⟩}`)". No Mathlib code is
vendored; the conversion follows Mathlib's characteristic-function and Fourier-character
normalizations.

## Main declarations

* `TauCeti.MeasureTheory.fourierConvention`: the finite-measure Fourier transform in the
  `e^{-2πi⟪a,q⟫}` convention.
* `TauCeti.MeasureTheory.fourierConvention_eq_charFun`: conversion to Mathlib's `charFun`.
* `TauCeti.MeasureTheory.norm_fourierConvention_le`: the finite-measure norm bound.
* `TauCeti.MeasureTheory.continuous_fourierConvention`: continuity for finite measures.
* `TauCeti.MeasureTheory.fourierConvention_isPositiveDefinite_of_star_eq_neg`: the finite-measure
  transform is positive definite for an explicit negation involution.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 4.
-/

public section

open MeasureTheory RealInnerProductSpace Complex

namespace TauCeti

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] {μ : Measure E}

/-- The Fourier transform of a finite measure in Mathlib's Fourier-analysis convention:
`a ↦ ∫ q, exp (-2π i ⟪a, q⟫) ∂μ q`. This is the convention used in the Bochner statement in the
OneParameterSemigroups roadmap. -/
@[expose]
noncomputable def fourierConvention (μ : Measure E) (a : E) : ℂ :=
  ∫ q, exp (-2 * Real.pi * I * (⟪a, q⟫ : ℂ)) ∂μ

/-- The pointwise integral expression for `fourierConvention`. -/
theorem fourierConvention_apply (a : E) :
    fourierConvention μ a = ∫ q, exp (-2 * Real.pi * I * (⟪a, q⟫ : ℂ)) ∂μ :=
  rfl

/-- The `e^{-2πi⟪a,q⟫}` Fourier convention is the characteristic function evaluated at
`-(2π) • a`. This is the named conversion between the Fourier convention and Mathlib's
`MeasureTheory.charFun` convention. -/
theorem fourierConvention_eq_charFun (a : E) :
    fourierConvention μ a = charFun μ (-(2 * Real.pi) • a) := by
  rw [fourierConvention_apply, charFun_apply]
  congr with q
  congr 1
  rw [inner_smul_right, real_inner_comm]
  norm_num
  ring

/-- The Fourier-convention transform at the origin is the total mass, as a complex number. -/
@[simp]
theorem fourierConvention_zero :
    fourierConvention μ 0 = μ.real Set.univ := by
  rw [fourierConvention_eq_charFun]
  simp

/-- The Fourier-convention transform of the zero measure is zero. -/
@[simp]
theorem fourierConvention_zero_measure (a : E) :
    fourierConvention (0 : Measure E) a = 0 := by
  rw [fourierConvention_eq_charFun]
  simp

/-- The Fourier-convention transform of a finite measure is bounded by the total mass. -/
theorem norm_fourierConvention_le (a : E) :
    ‖fourierConvention μ a‖ ≤ μ.real Set.univ := by
  rw [fourierConvention_eq_charFun]
  exact norm_charFun_le (μ := μ) (-(2 * Real.pi) • a)

/-- The Fourier-convention transform of a probability measure has norm at most one. -/
theorem norm_fourierConvention_le_one [IsProbabilityMeasure μ] (a : E) :
    ‖fourierConvention μ a‖ ≤ 1 :=
  (norm_fourierConvention_le (μ := μ) a).trans_eq (by simp)

section Topology

variable [BorelSpace E] [IsFiniteMeasure μ]

/-- In the explicit negation-involution convention, the Fourier-convention transform of a finite
measure is positive definite. -/
theorem fourierConvention_isPositiveDefinite_of_star_eq_neg [StarAddMonoid E]
    (hstar : ∀ x : E, star x = -x) :
    IsPositiveDefinite (fourierConvention μ) := by
  rw [show fourierConvention μ = fun a : E => charFun μ (-(2 * Real.pi) • a) by
    ext a
    exact fourierConvention_eq_charFun (μ := μ) a]
  exact (charFun_isPositiveDefinite_of_star_eq_neg (μ := μ) hstar).comp_addMonoidHom
    (DistribSMul.toAddMonoidHom E (-(2 * Real.pi))) (by
      intro x
      simp [hstar])

variable [SecondCountableTopology E]

/-- The Fourier-convention transform of a finite measure is continuous. -/
theorem continuous_fourierConvention : Continuous (fourierConvention μ) := by
  rw [show fourierConvention μ = fun a : E => charFun μ (-(2 * Real.pi) • a) by
    ext a
    exact fourierConvention_eq_charFun (μ := μ) a]
  exact MeasureTheory.continuous_charFun.comp (continuous_const.smul continuous_id)

/-- The Fourier-convention transform of a finite measure is continuous and positive definite under
an explicit negation involution. -/
theorem continuous_fourierConvention_and_isPositiveDefinite_of_star_eq_neg [StarAddMonoid E]
    (hstar : ∀ x : E, star x = -x) :
    Continuous (fourierConvention μ) ∧ IsPositiveDefinite (fourierConvention μ) :=
  ⟨continuous_fourierConvention, fourierConvention_isPositiveDefinite_of_star_eq_neg hstar⟩

end Topology

end MeasureTheory

end TauCeti
