/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Uniform.Ball.Basic
import TauCeti.MeasureTheory.Measure.Dirac
import TauCeti.MeasureTheory.Measure.WithDensity
import TauCeti.Probability.Distributions.Uniform.Basic

/-!
# Topological support of uniform ball laws

The uniform law on an open ball has the whole closed ball as its topological support.
Boundary points belong to the support even though the law is concentrated on the open ball.
The same formula includes the point mass at radius zero, the zero measure at negative radii,
and zero-dimensional spaces.

For positive radii, the closed ball is also the closure of the uniform density's nonzero locus
(see `MeasureTheory.Measure.support_withDensity_eq_closure`).
-/

public section

open MeasureTheory Metric Set

namespace TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The topological support of a uniform ball law is the closed ball, for every real radius.
At radius zero this is the singleton center; at negative radii both sets are empty. -/
@[simp]
theorem support_uniformBallMeasure (c : E) (r : ℝ) :
    (uniformBallMeasure c r).support = closedBall c r := by
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · simp [uniformBallMeasure_of_neg hr, closedBall_eq_empty.2 hr]
  · simp [Measure.support_dirac]
  · rw [uniformBallMeasure_eq_withDensity hr.ne', ← closure_ball c hr.ne']
    apply Measure.support_withDensity_eq_closure
      (measurable_uniformPDF measurableSet_ball volume) isOpen_ball
    simp [pdf.uniformPDF, Pi.smul_def, Set.support_indicator,
      Function.support_const (ENNReal.inv_ne_zero.2 measure_ball_lt_top.ne)]

end TauCeti.Probability
