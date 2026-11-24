/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Harmonic.MeanValue

/-!
# Circle means bounded by a harmonic majorant

Mathlib's mean value property writes the value of a planar harmonic function at the center of a
disk as its circle average. This file uses it to bound the interior circle means of a continuous
function on the open unit disk by the value at the origin of any real harmonic majorant.

## Main declarations

* `TauCeti.circleAverage_le_of_harmonic_majorant`: a harmonic majorant `u` of a continuous
  function `g` on the open unit disk satisfies `circleAverage g 0 r ≤ u 0` for `|r| < 1`.
-/

public section

namespace TauCeti

/-- A real harmonic majorant `u` of a continuous real function `g` on the open unit disk bounds
each interior circle mean of `g` by its value at the origin. No boundary regularity of the majorant
is required. -/
theorem circleAverage_le_of_harmonic_majorant {g : ℂ → ℝ}
    (hg : ContinuousOn g (Metric.ball 0 1)) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u (Metric.ball 0 1))
    (hmajor : ∀ w ∈ Metric.ball (0 : ℂ) 1, g w ≤ u w) {r : ℝ} (hr : |r| < 1) :
    Real.circleAverage g 0 r ≤ u 0 := by
  have hsub : Metric.closedBall (0 : ℂ) |r| ⊆ Metric.ball 0 1 :=
    Metric.closedBall_subset_ball hr
  have hus := hu.mono hsub
  rw [← hus.circleAverage_eq (R := r)]
  apply Real.circleAverage_mono
  · exact (hg.mono (Metric.sphere_subset_closedBall.trans hsub)).circleIntegrable'
  · exact (hus.continuousOn.mono Metric.sphere_subset_closedBall).circleIntegrable'
  · intro w hw
    exact hmajor w (hsub (Metric.sphere_subset_closedBall hw))

end TauCeti
