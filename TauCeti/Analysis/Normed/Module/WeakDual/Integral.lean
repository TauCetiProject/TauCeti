/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.WeakDual.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrability on weak-star dual balls

On the weak-star closed dual ball of radius `r`, every functional `φ` satisfies
`‖φ x‖ ≤ r * ‖x‖`, so the continuous function `φ ↦ ‖φ x‖ ^ p` is bounded. It is therefore
integrable against every finite measure on the ball for an opens-measurable structure on the weak
dual. These are the integrands of Pietsch domination.

Moreover, joint evaluation `(a, φ) ↦ ‖(φ : WeakDual 𝕜 E) (Φ a)‖ ^ q` is measurable on
`α × WeakDual.closedBall 𝕜 E r` whenever `Φ : α → E` is measurable, and is integrable against
`μ.prod ν` for any finite measure `ν` on `WeakDual.closedBall 𝕜 E r` whenever `‖Φ ·‖ ^ q` is
`μ`-integrable.

## Main results

* `MeasureTheory.Measure.integrable_norm_apply_rpow`: for a finite measure `ν` on a weak-star
  closed dual ball, `φ ↦ ‖φ x‖ ^ p` is `ν`-integrable.
* `MeasureTheory.measurable_norm_apply_closedBall_rpow`,
  `MeasureTheory.measurable_norm_apply_closedBall_sq`: joint measurability of `‖φ (Φ a)‖ ^ q`
  and `‖φ (Φ a)‖ ^ 2`.
* `MeasureTheory.Measure.integrable_norm_apply_closedBall_rpow`,
  `MeasureTheory.Measure.integrable_norm_apply_closedBall_sq`: product integrability of
  `‖φ (Φ a)‖ ^ q` and `‖φ (Φ a)‖ ^ 2` against `μ.prod ν`.
-/

public section

open Metric MeasureTheory
open scoped ENNReal

namespace MeasureTheory

variable {α 𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [MeasurableSpace α] [MeasurableSpace E] [OpensMeasurableSpace E]
  [MeasurableSpace (WeakDual 𝕜 E)] [OpensMeasurableSpace (WeakDual 𝕜 E)]

/-- Joint evaluation `(a, φ) ↦ ‖(φ : WeakDual 𝕜 E) (Φ a)‖ ^ q` is measurable on
`α × WeakDual.closedBall 𝕜 E r` when `Φ : α → E` is measurable and `0 ≤ q`. -/
theorem measurable_norm_apply_closedBall_rpow (r q : ℝ)
    [SecondCountableTopologyEither E (WeakDual.closedBall 𝕜 E r)]
    {Φ : α → E} (hΦ : Measurable Φ) :
    Measurable fun p : α × WeakDual.closedBall 𝕜 E r ↦
      ‖(p.2 : WeakDual 𝕜 E) (Φ p.1)‖ ^ q := by
  have heval : Measurable fun p : E × WeakDual.closedBall 𝕜 E r ↦
      ‖(p.2 : WeakDual 𝕜 E) p.1‖ :=
    (WeakDual.continuous_eval_closedBall (𝕜 := 𝕜) (E := E) r).norm.measurable
  exact (heval.comp (hΦ.prodMap measurable_id)).pow_const q

/-- Joint evaluation `(a, φ) ↦ ‖(φ : WeakDual 𝕜 E) (Φ a)‖ ^ 2` is measurable on
`α × WeakDual.closedBall 𝕜 E r` when `Φ : α → E` is measurable. -/
theorem measurable_norm_apply_closedBall_sq (r : ℝ)
    [SecondCountableTopologyEither E (WeakDual.closedBall 𝕜 E r)]
    {Φ : α → E} (hΦ : Measurable Φ) :
    Measurable fun p : α × WeakDual.closedBall 𝕜 E r ↦
      ‖(p.2 : WeakDual 𝕜 E) (Φ p.1)‖ ^ 2 := by
  have heval : Measurable fun p : E × WeakDual.closedBall 𝕜 E r ↦
      ‖(p.2 : WeakDual 𝕜 E) p.1‖ ^ 2 :=
    ((WeakDual.continuous_eval_closedBall (𝕜 := 𝕜) (E := E) r).norm.pow 2).measurable
  exact heval.comp (hΦ.prodMap measurable_id)

end MeasureTheory

namespace MeasureTheory.Measure

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- For a finite measure on a weak-star closed dual ball, each function `φ ↦ ‖φ x‖ ^ p` is
integrable. -/
theorem integrable_norm_apply_rpow [MeasurableSpace (WeakDual 𝕜 E)]
    [OpensMeasurableSpace (WeakDual 𝕜 E)] {r : ℝ} (ν : Measure (WeakDual.closedBall 𝕜 E r))
    [IsFiniteMeasure ν] (p : ℝ≥0∞) (x : E) :
    Integrable (fun φ : WeakDual.closedBall 𝕜 E r ↦ ‖(φ : WeakDual 𝕜 E) x‖ ^ p.toReal) ν := by
  have h : Integrable (fun φ ↦ WeakDual.evalRpow r p x φ) ν :=
    Integrable.of_bound (WeakDual.evalRpow r p x).continuous.aestronglyMeasurable
      ((r * ‖x‖) ^ p.toReal) (ae_of_all _ fun φ ↦ by
        have hφ : ‖(φ : WeakDual 𝕜 E) x‖ ≤ r * ‖x‖ :=
          WeakDual.norm_apply_le_of_mem_closedBall φ x
        simpa only [WeakDual.evalRpow_apply, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using
            Real.rpow_le_rpow (norm_nonneg _) hφ ENNReal.toReal_nonneg)
  simpa only [WeakDual.evalRpow_apply] using h

/-- For a measurable map `Φ : α → E` with `‖Φ ·‖ ^ q` integrable under `μ` and a finite measure
`ν` on `WeakDual.closedBall 𝕜 E r` (`r ≥ 0`, `q ≥ 0`), the joint evaluation
`(a, φ) ↦ ‖φ (Φ a)‖ ^ q` is integrable against `μ.prod ν`. -/
theorem integrable_norm_apply_closedBall_rpow {α : Type*} [MeasurableSpace α]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    [MeasurableSpace (WeakDual 𝕜 E)] [OpensMeasurableSpace (WeakDual 𝕜 E)]
    {r : ℝ} (hr : 0 ≤ r) {q : ℝ} (hq : 0 ≤ q) (μ : Measure α)
    (ν : Measure (WeakDual.closedBall 𝕜 E r)) [IsFiniteMeasure ν]
    [SecondCountableTopologyEither E (WeakDual.closedBall 𝕜 E r)]
    {Φ : α → E} (hΦ : Measurable Φ) (hΦ_int : Integrable (fun a ↦ ‖Φ a‖ ^ q) μ) :
    Integrable (fun p : α × WeakDual.closedBall 𝕜 E r ↦
      ‖(p.2 : WeakDual 𝕜 E) (Φ p.1)‖ ^ q) (μ.prod ν) := by
  have hdom : Integrable (fun p : α × WeakDual.closedBall 𝕜 E r ↦ r ^ q * ‖Φ p.1‖ ^ q)
      (μ.prod ν) :=
    (hΦ_int.const_mul (r ^ q)).comp_fst ν
  refine hdom.mono' (measurable_norm_apply_closedBall_rpow r q hΦ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p ↦ ?_)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), ← Real.mul_rpow hr (norm_nonneg _)]
  exact Real.rpow_le_rpow (norm_nonneg _) (WeakDual.norm_apply_le_of_mem_closedBall p.2 (Φ p.1)) hq

/-- For a measurable map `Φ : α → E` with `‖Φ ·‖ ^ 2` integrable under `μ` and a finite measure
`ν` on `WeakDual.closedBall 𝕜 E r`, the squared joint evaluation `(a, φ) ↦ ‖φ (Φ a)‖ ^ 2` is
integrable against `μ.prod ν`. -/
theorem integrable_norm_apply_closedBall_sq {α : Type*} [MeasurableSpace α]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    [MeasurableSpace (WeakDual 𝕜 E)] [OpensMeasurableSpace (WeakDual 𝕜 E)]
    {r : ℝ} (μ : Measure α) (ν : Measure (WeakDual.closedBall 𝕜 E r)) [IsFiniteMeasure ν]
    [SecondCountableTopologyEither E (WeakDual.closedBall 𝕜 E r)]
    {Φ : α → E} (hΦ : Measurable Φ) (hΦ_int : Integrable (fun a ↦ ‖Φ a‖ ^ 2) μ) :
    Integrable (fun p : α × WeakDual.closedBall 𝕜 E r ↦
      ‖(p.2 : WeakDual 𝕜 E) (Φ p.1)‖ ^ 2) (μ.prod ν) := by
  have hdom : Integrable (fun p : α × WeakDual.closedBall 𝕜 E r ↦ r ^ 2 * ‖Φ p.1‖ ^ 2)
      (μ.prod ν) :=
    (hΦ_int.const_mul (r ^ 2)).comp_fst ν
  refine hdom.mono' (measurable_norm_apply_closedBall_sq r hΦ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p ↦ ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (WeakDual.norm_apply_le_of_mem_closedBall p.2 (Φ p.1)) 2

end MeasureTheory.Measure
