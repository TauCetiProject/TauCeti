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
finite measure, and the characteristic function of a measure that is not finite vanishes, so that
the characteristic function of every measure is continuous. These facts support integral
manipulations in characteristic-function formulas and positive-definiteness proofs.
-/

public section

open MeasureTheory BoundedContinuousFunction RealInnerProductSpace Complex

namespace TauCeti

section Inner

variable {E : Type*} [Inner ℝ E] [MeasurableSpace E] {μ : Measure E}

/-- The characteristic function of a measure that is not finite is zero: the kernel has norm `1`,
so it is not integrable, and the Bochner integral of a non-integrable function is zero. -/
@[simp]
theorem charFun_of_not_isFiniteMeasure (hμ : ¬ IsFiniteMeasure μ) : charFun μ = 0 := by
  refine funext fun t => integral_undef fun h => hμ ?_
  have h1 : Integrable (fun _ : E => (1 : ℝ)) μ := by
    simpa [Complex.norm_exp_ofReal_mul_I] using h.norm
  exact (integrable_const_iff_isFiniteMeasure one_ne_zero).mp h1

end Inner

section InnerProductSpace

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E}

/-- The characteristic function of any measure on a real inner product space is continuous: for a
finite measure by dominated convergence, with the constant bound `1` for the kernel, and otherwise
because it vanishes (`TauCeti.charFun_of_not_isFiniteMeasure`). -/
@[fun_prop]
theorem continuous_charFun_of_opensMeasurableSpace : Continuous (charFun μ) := by
  by_cases hμ : IsFiniteMeasure μ
  · simp_rw [funext charFun_apply]
    refine continuous_of_dominated (bound := fun _ ↦ 1)
      (fun t ↦ ?_) (fun t ↦ ?_) (integrable_const 1) (ae_of_all _ fun x ↦ ?_)
    · exact (by fun_prop : Continuous fun x : E ↦
        Complex.exp (inner ℝ x t * Complex.I)).aestronglyMeasurable
    · exact ae_of_all _ fun x ↦ (Complex.norm_exp_ofReal_mul_I _).le
    · fun_prop
  · rw [charFun_of_not_isFiniteMeasure hμ]
    exact continuous_zero

variable [IsFiniteMeasure μ]

/-- The characteristic-function kernel is integrable against every finite measure. -/
theorem integrable_exp_inner_mul_I (a : E) :
    Integrable (fun y => exp (⟪y, a⟫ * I)) μ :=
  ((innerProbChar a).integrable μ).congr (.of_forall (innerProbChar_apply a))

end InnerProductSpace

end TauCeti
