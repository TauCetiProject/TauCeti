/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Fourier-convention bridge for measures

Mathlib's Fourier transform uses the character `x ↦ exp (2π i x)`, while Mathlib's
characteristic function of a measure is `t ↦ ∫ q, exp (i ⟪q, t⟫) ∂μ q`. Bochner-type
statements are often written in the Fourier-transform convention

`a ↦ ∫ q, exp (-2π i ⟪a, q⟫) ∂μ q`.

This file documents the exact conversion from Mathlib's Fourier integral to
`MeasureTheory.charFun`: at frequency `a`, it is `charFun μ (-(2π) • a)`.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, the API bullet asking for
"a stated Fourier-convention conversion lemma between Mathlib's `2π` form
(`e^{-2πi⟨·,·⟩}`) and the characteristic-function form (`e^{i⟨·,·⟩}`)". No Mathlib code is
vendored; the conversion follows Mathlib's characteristic-function and Fourier-character
normalizations.

## Checked conversion

The example below verifies the conversion directly from Mathlib's
`MeasureTheory.charFun_eq_fourierIntegral'`.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 4.
-/

public section

open MeasureTheory RealInnerProductSpace Complex

namespace TauCeti

namespace MeasureTheory

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] {μ : Measure E}

example (a : E) :
    VectorFourier.fourierIntegral Real.fourierChar μ (innerₗ E) (1 : E → ℂ) a =
      charFun μ (-(2 * Real.pi) • a) := by
  rw [charFun_eq_fourierIntegral']
  congr 1
  rw [smul_smul]
  have h : Real.pi⁻¹ * 2⁻¹ * (2 * Real.pi) = (1 : ℝ) := by
    field_simp [Real.pi_ne_zero]
  simp [h]

end MeasureTheory

end TauCeti
