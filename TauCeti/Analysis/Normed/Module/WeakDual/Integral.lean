/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.WeakDual.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Integrability on weak-star dual balls

On the weak-star closed dual ball of radius `r`, every functional `φ` satisfies
`‖φ x‖ ≤ r * ‖x‖`, so the continuous function `φ ↦ ‖φ x‖ ^ p` is bounded. It is therefore
integrable against every finite measure on the ball for an opens-measurable structure on the weak
dual. These are the integrands of Pietsch domination.

## Main results

* `MeasureTheory.Measure.integrable_norm_apply_rpow`: for a finite measure `ν` on a weak-star
  closed dual ball, `φ ↦ ‖φ x‖ ^ p` is `ν`-integrable.
-/

public section

open Metric MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- For a finite measure on a weak-star closed dual ball, each function `φ ↦ ‖φ x‖ ^ p` is
integrable. -/
theorem integrable_norm_apply_rpow [MeasurableSpace (WeakDual 𝕜 E)]
    [OpensMeasurableSpace (WeakDual 𝕜 E)] {r : ℝ}
    (ν : Measure (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) r))
    [IsFiniteMeasure ν] (p : ℝ≥0∞) (x : E) :
    Integrable (fun φ : WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual 𝕜 E) r ↦
      ‖(φ : WeakDual 𝕜 E) x‖ ^ p.toReal) ν := by
  have h : Integrable (fun φ ↦ WeakDual.evalRpow r p x φ) ν :=
    Integrable.of_bound (WeakDual.evalRpow r p x).continuous.aestronglyMeasurable
      ((r * ‖x‖) ^ p.toReal) (ae_of_all _ fun φ ↦ by
        have hφ : ‖(φ : WeakDual 𝕜 E) x‖ ≤ r * ‖x‖ :=
          (WeakDual.toStrongDual (φ : WeakDual 𝕜 E)).le_of_opNorm_le
            (mem_closedBall_zero_iff.1 φ.2) x
        simpa only [WeakDual.evalRpow_apply, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using
            Real.rpow_le_rpow (norm_nonneg _) hφ ENNReal.toReal_nonneg)
  simpa only [WeakDual.evalRpow_apply] using h

end MeasureTheory.Measure
