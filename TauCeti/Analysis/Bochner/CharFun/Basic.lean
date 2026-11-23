/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Characteristic functions: kernel integrability, vanishing and continuity

The complex exponential kernel of a characteristic function is integrable against every finite
measure (`TauCeti.integrable_exp_inner_mul_I`). The characteristic function of a measure that is
not finite is zero (`TauCeti.charFun_of_not_isFiniteMeasure`). On a real inner product space whose
open sets are measurable (`[OpensMeasurableSpace E]`), the characteristic function of every
measure is continuous (`TauCeti.continuous_charFun_of_opensMeasurableSpace`). On the real line,
the average of `cos (t * (x - v))` over a finite measure is the real part of its characteristic
function at `t`, rotated by the phase `-t * v` (`TauCeti.integral_cos_mul_sub_eq_re`). These facts
support integral manipulations in characteristic-function formulas and positive-definiteness
proofs.
-/

public section

open MeasureTheory BoundedContinuousFunction RealInnerProductSpace Complex

namespace TauCeti

section Inner

variable {E : Type*} [Inner ℝ E] [MeasurableSpace E] {μ : Measure E}

/-- The characteristic function of a measure that is not finite is zero, the value Mathlib's
Bochner integral gives a non-integrable function. -/
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

/-- The characteristic function of every measure on a real inner product space with
`[OpensMeasurableSpace E]` is continuous. This weakens Mathlib's `MeasureTheory.continuous_charFun`,
which asks for a finite measure on a normed, second-countable Borel space: here the space need only
be seminormed with measurable open sets, and the measure need not be finite (if it is not, its
characteristic function is zero). -/
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

section Real

variable {μ : Measure ℝ} [IsFiniteMeasure μ]

/-- The average of `cos (t * (x - v))` over a finite measure `μ` on `ℝ` is the real part of the
characteristic function at `t`, rotated by the phase `-t * v`. The rotation comes from translating
`μ` by `-v` (Mathlib's `MeasureTheory.charFun_map_add_const`). -/
theorem integral_cos_mul_sub_eq_re (v t : ℝ) :
    ∫ x, Real.cos (t * (x - v)) ∂μ = (cexp (↑(-(t * v)) * I) * charFun μ t).re := by
  have hint : Integrable (fun x : ℝ ↦ cexp (↑(t * (x - v)) * I)) μ :=
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x ↦ by rw [norm_exp_ofReal_mul_I])
  have hshift : ∫ x, cexp (↑(t * (x - v)) * I) ∂μ = cexp (↑(-(t * v)) * I) * charFun μ t :=
    calc ∫ x, cexp (↑(t * (x - v)) * I) ∂μ = charFun (μ.map (· + -v)) t := by
          rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
          simp [sub_eq_add_neg]
      _ = cexp (↑(-(t * v)) * I) * charFun μ t := by
          rw [charFun_map_add_const, Real.inner_apply, neg_mul, mul_comm v t, mul_comm]
  rw [← hshift, ← RCLike.re_eq_complex_re, ← integral_re hint]
  simp only [RCLike.re_eq_complex_re, exp_ofReal_mul_I_re]

end Real

end TauCeti
