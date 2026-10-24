/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Cycle.Basic
public import TauCeti.Analysis.Contour.Curve.Circle
public import TauCeti.Analysis.Contour.Winding.Number.Circle

/-!
# Circles as contour cycles

The counterclockwise circle `circleMap c R` on `[0, 2π]` is a closed `C¹` curve. This file packages
it as a one-generator contour cycle and identifies its cycle invariants with the classical ones:
the cycle integral is Mathlib's circle integral `∮ z in C(c, R), f z`, the trace is the sphere of
radius `|R|`, and the winding number is `1` inside the disc and `0` outside it.

Circles are the comparison cycles for cycle integrals whose integrand is controlled near infinity,
such as Banach-algebra resolvents.

## Main definitions

* `TauCeti.Contour.circleCurve`: the circle as a closed piecewise-`C¹` curve.
* `TauCeti.Contour.circleCycle`: the corresponding one-generator contour cycle.

## Main results

* `TauCeti.Contour.Cycle.integral_circleCycle`: its cycle integral is the circle integral.
* `TauCeti.Contour.Cycle.trace_circleCycle`: its trace is the sphere.
* `TauCeti.Contour.Cycle.windingNumber_circleCycle_eq_one_of_dist_lt`,
  `TauCeti.Contour.Cycle.windingNumber_circleCycle_eq_zero_of_lt_dist`: its winding numbers.
-/

public section

noncomputable section

open Metric Set

namespace TauCeti.Contour

/-- The counterclockwise circle `circleMap c R` on `[0, 2π]`, bundled as a closed piecewise-`C¹`
curve. -/
def circleCurve (c : ℂ) (R : ℝ) : PiecewiseC1ClosedCurve :=
  PiecewiseC1ClosedCurve.of (circleMap c R)
    (IsPiecewiseC1On.of_contDiffOn (contDiff_circleMap c R).contDiffOn)
    (by simpa using (periodic_circleMap c R 0).symm)

/-- The counterclockwise circle `circleMap c R` on `[0, 2π]` as a one-generator contour cycle. -/
def circleCycle (c : ℂ) (R : ℝ) : Cycle :=
  FreeAbelianGroup.of (circleCurve c R)

namespace Cycle

/-- Integrating over the circle cycle gives Mathlib's circle integral. -/
@[simp]
theorem integral_circleCycle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (c : ℂ) (R : ℝ) :
    integral f (circleCycle c R) = ∮ z in C(c, R), f z := by
  rw [circleCycle, circleCurve, integral_of_raw, circleIntegral]

/-- The trace of the circle cycle is the sphere of radius `|R|`. -/
@[simp]
theorem trace_circleCycle (c : ℂ) (R : ℝ) : trace (circleCycle c R) = sphere c |R| := by
  rw [circleCycle, circleCurve, trace_of_raw, Complex.image_circleMap_uIcc]

/-- The circle cycle winds once around every point inside its disc. -/
theorem windingNumber_circleCycle_eq_one_of_dist_lt {c w : ℂ} {R : ℝ} (hw : dist w c < R) :
    windingNumber w (circleCycle c R) = 1 := by
  rw [circleCycle, circleCurve, windingNumber_of_raw,
    Contour.windingNumber_circleMap_eq_one_of_dist_lt hw]

/-- The circle cycle does not wind around points outside its closed disc. -/
theorem windingNumber_circleCycle_eq_zero_of_lt_dist {c w : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hw : R < dist w c) : windingNumber w (circleCycle c R) = 0 := by
  rw [circleCycle, circleCurve, windingNumber_of_raw,
    Contour.windingNumber_circleMap_eq_zero_of_lt_dist hR hw]

end Cycle

end TauCeti.Contour
