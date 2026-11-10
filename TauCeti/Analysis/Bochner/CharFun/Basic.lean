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
finite measure, and the characteristic function of a measure that is not finite vanishes. These
facts support integral manipulations in characteristic-function formulas and positive-definiteness
proofs.
-/

public section

open MeasureTheory BoundedContinuousFunction RealInnerProductSpace Complex

namespace TauCeti

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E} [IsFiniteMeasure μ]

omit [OpensMeasurableSpace E] [IsFiniteMeasure μ] in
/-- The characteristic function of a measure that is not finite is zero: the kernel has norm `1`,
so it is not integrable, and the Bochner integral of a non-integrable function is zero. -/
theorem charFun_of_not_isFiniteMeasure (hμ : ¬ IsFiniteMeasure μ) : charFun μ = 0 := by
  refine funext fun t => integral_undef fun h => hμ ?_
  have h1 : Integrable (fun _ : E => (1 : ℝ)) μ := by
    simpa [Complex.norm_exp_ofReal_mul_I] using h.norm
  exact (integrable_const_iff_isFiniteMeasure one_ne_zero).mp h1

/-- The characteristic-function kernel is integrable against every finite measure. -/
theorem integrable_exp_inner_mul_I (a : E) :
    Integrable (fun y => exp (⟪y, a⟫ * I)) μ :=
  ((innerProbChar a).integrable μ).congr (.of_forall (innerProbChar_apply a))

end TauCeti
