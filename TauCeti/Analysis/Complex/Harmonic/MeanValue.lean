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
disk as its circle average. This file uses it to bound the circle average of a real function by
the value at the center of any real harmonic function majorizing it on the circle.

## Main declarations

* `TauCeti.circleAverage_le_of_harmonic_majorant`: if `u` is harmonic near `closedBall c |R|`
  and `g ≤ u` on `sphere c |R|`, then `circleAverage g c R ≤ u c`.
-/

public section

namespace TauCeti

/-- A real function `g` lying below a real harmonic function `u` on a circle has circle average
at most the value of `u` at the center, provided `g` is circle integrable and `u` is harmonic near
the closed disk. -/
theorem circleAverage_le_of_harmonic_majorant {g u : ℂ → ℝ} {c : ℂ} {R : ℝ}
    (hg : CircleIntegrable g c R)
    (hu : InnerProductSpace.HarmonicOnNhd u (Metric.closedBall c |R|))
    (hmajor : ∀ w ∈ Metric.sphere c |R|, g w ≤ u w) :
    Real.circleAverage g c R ≤ u c := by
  rw [← hu.circleAverage_eq]
  exact Real.circleAverage_mono hg
    ((hu.continuousOn.mono Metric.sphere_subset_closedBall).circleIntegrable') hmajor

end TauCeti
