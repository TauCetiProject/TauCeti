/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Linear change of variables for the Fourier transform

Precomposing a function by a continuous real linear automorphism rescales its Fourier transform
by the inverse absolute determinant and precomposes it by the adjoint of the inverse. This is the
change of coordinates needed to transport Fourier identities from the standard integer lattice
to an arbitrary full lattice.

The Jacobian factor comes from Mathlib's
`MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar`. The formulas use the total Bochner
integral, so no integrability hypothesis is necessary. They apply to functions with values in any
complex normed space, including Schwartz functions by coercion.

## Main results

* `ContinuousLinearEquiv.fourier_comp`: change of variables for the Fourier transform.
* `ContinuousLinearEquiv.fourierInv_comp`: the corresponding inverse-transform formula.
-/

public section

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Fourier change of variables under a real linear automorphism. The frequency transforms by
the adjoint of the inverse, and the scalar is the inverse absolute determinant. -/
theorem _root_.ContinuousLinearEquiv.fourier_comp (A : E ≃L[ℝ] E) (f : E → F) (y : E) :
    𝓕 (f ∘ A) y = |A.toLinearEquiv.toLinearMap.det|⁻¹ •
      𝓕 f (ContinuousLinearMap.adjoint (A.symm : E →L[ℝ] E) y) := by
  have hinner (x : E) :
      ⟪A x, ContinuousLinearMap.adjoint (A.symm : E →L[ℝ] E) y⟫ = ⟪x, y⟫ := by
    simp [ContinuousLinearMap.adjoint_inner_right]
  simp only [Real.fourier_eq, Function.comp_apply]
  simp_rw [← hinner]
  have hcov := integral_map_equiv (μ := volume) A.toHomeomorph.toMeasurableEquiv
    (fun x : E ↦ 𝐞 (-⟪x, ContinuousLinearMap.adjoint (A.symm : E →L[ℝ] E) y⟫) • f x)
  simp only [Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph] at hcov
  rw [← hcov]
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar volume
    A.toLinearEquiv.isUnit_det'.ne_zero
  simp only [LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv] at hmap
  rw [hmap, integral_smul_measure]
  simp [abs_inv]

/-- The inverse Fourier transform has the same linear change-of-variables law. -/
theorem _root_.ContinuousLinearEquiv.fourierInv_comp (A : E ≃L[ℝ] E) (f : E → F) (y : E) :
    𝓕⁻ (f ∘ A) y = |A.toLinearEquiv.toLinearMap.det|⁻¹ •
      𝓕⁻ f (ContinuousLinearMap.adjoint (A.symm : E →L[ℝ] E) y) := by
  simp only [Real.fourierInv_eq_fourier_neg, A.fourier_comp, map_neg]

end TauCeti
