/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Alternating
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import TauCeti.Analysis.Matrix.MeasurableSpace

/-!
# Measurability of the sign of a change of frame

The sign `TauCeti.frameSign (σ x) (τ x)` of the change of frame between two measurable fields of
frames is measurable (`Measurable.frameSign`): it is read off from the overlap determinant
`det (⟪σ x i, τ x j⟫)`, a polynomial in measurable inner products.
-/

public section

open scoped RealInnerProductSpace

variable {E X ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace X] [Fintype ι] [DecidableEq ι]

/-- The sign of the change of frame between two measurable fields of frames is measurable. -/
@[fun_prop]
theorem Measurable.frameSign {σ τ : X → ι → E} (hσ : Measurable σ) (hτ : Measurable τ) :
    Measurable fun x ↦ TauCeti.frameSign (σ x) (τ x) := by
  simp only [TauCeti.frameSign_def]
  exact Measurable.ite (measurableSet_le measurable_const (by fun_prop)) measurable_const
    measurable_const
