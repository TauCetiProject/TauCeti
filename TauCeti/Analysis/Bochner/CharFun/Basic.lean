/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Integrability of the characteristic-function kernel

The complex exponential kernel of a characteristic function is integrable against every
finite measure. This fact supports integral manipulations in characteristic-function formulas
and positive-definiteness proofs.
-/

public section

open MeasureTheory BoundedContinuousFunction RealInnerProductSpace Complex

namespace TauCeti

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E} [IsFiniteMeasure μ]

/-- The characteristic-function kernel is integrable against every finite measure. -/
theorem integrable_exp_inner_mul_I (a : E) :
    Integrable (fun y => exp (⟪y, a⟫ * I)) μ :=
  ((innerProbChar a).integrable μ).congr (.of_forall (innerProbChar_apply a))

end TauCeti
