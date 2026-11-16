/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import TauCeti.MeasureTheory.Function.L2Space

/-!
# The Fourier transform of pointwise adjoints

For a function `f` on a finite-dimensional real inner product space with values in operators
`V →L[ℂ] W` between complex Hilbert spaces, the Fourier transform of the pointwise Hilbert space
adjoint `z ↦ (f z)†` is the adjoint of the Fourier transform of `f` at the reflected frequency:
`𝓕 (f†) w = (𝓕 f (-w))†`. This is the operator-valued counterpart of the conjugation rule
`𝓕 (conj f) w = conj (𝓕 f (-w))` for scalar functions.

## Main declarations

* `Real.fourier_adjoint`: `𝓕 (z ↦ (f z)†) w = (𝓕 f (-w))†`.
-/

public section

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace Real

variable {E V W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- The Fourier transform of the pointwise adjoint of an operator-valued function is the adjoint of
its Fourier transform at the reflected frequency: `𝓕 (f†) w = (𝓕 f (-w))†`. No integrability is
needed, since the adjoint commutes with every integral (`ContinuousLinearMap.integral_adjoint`). -/
theorem fourier_adjoint (f : E → V →L[ℂ] W) (w : E) :
    𝓕 (fun z ↦ ContinuousLinearMap.adjoint (f z)) w = ContinuousLinearMap.adjoint (𝓕 f (-w)) := by
  rw [fourier_eq, fourier_eq, ← ContinuousLinearMap.integral_adjoint]
  refine integral_congr_ae (.of_forall fun z ↦ ?_)
  simp only [Circle.smul_def, map_smulₛₗ, ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv,
    inner_neg_right, neg_neg]

end Real
