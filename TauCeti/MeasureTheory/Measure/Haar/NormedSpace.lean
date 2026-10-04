/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Additive Haar measures on real normed spaces

A continuous linear equivalence between finite-dimensional real normed spaces is nonsingular for
any additive Haar measures chosen on its source and target: null sets correspond to null sets
under it, whatever the normalizations. This is uniqueness of additive Haar measure, in the form
`MeasureTheory.Measure.absolutelyContinuous_isAddHaarMeasure`, applied to the pushforward measure,
which is again an additive Haar measure.

The real measure of a positive-radius ball is its radius raised to the dimension times the
real measure of the unit ball, independently of its centre.

## Main results

* `ContinuousLinearEquiv.quasiMeasurePreserving_addHaar`: a continuous linear equivalence
  is quasi measure preserving for additive Haar measures on its source and target.
* `MeasureTheory.Measure.addHaar_real_ball_of_pos`: the real measure of a positive-radius ball.
-/

public section

open MeasureTheory MeasureTheory.Measure Metric Module

namespace TauCeti

/-- A continuous linear equivalence is nonsingular for any additive Haar measures on its source
and target. -/
theorem _root_.ContinuousLinearEquiv.quasiMeasurePreserving_addHaar {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (e : E ≃L[ℝ] F) (μ : Measure E) (ν : Measure F)
    [IsAddHaarMeasure μ] [IsAddHaarMeasure ν] : QuasiMeasurePreserving e μ ν :=
  ⟨e.continuous.measurable, absolutelyContinuous_isAddHaarMeasure (μ.map e) ν⟩

/-- The real measure of a ball of positive radius is the corresponding power of the radius times
the real measure of the unit ball. -/
theorem _root_.MeasureTheory.Measure.addHaar_real_ball_of_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (mu : Measure E) [mu.IsAddHaarMeasure]
    (x : E) {r : ℝ} (hr : 0 < r) :
    mu.real (ball x r) = r ^ finrank ℝ E * mu.real (ball 0 1) := by
  rw [measureReal_def, mu.addHaar_ball_of_pos x hr, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ← measureReal_def]

end TauCeti

end
