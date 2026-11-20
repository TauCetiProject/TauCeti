/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Cycle.Basic
public import TauCeti.Analysis.Contour.Cycle.Winding
public import TauCeti.Analysis.Contour.Curve.Circle.Basic
public import TauCeti.Analysis.Contour.Winding.Number.Circle.Basic

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
* `TauCeti.Contour.Cycle.windingWeight_circleCycle`: for `R ≥ 0`, its trace-zero winding weight is
  the indicator of `ball c R`.
-/

public section

noncomputable section

open Metric Set

open scoped Real

namespace TauCeti.Contour

/-- The counterclockwise circle `circleMap c R` on `[0, 2π]`, bundled as a closed piecewise-`C¹`
curve. -/
def circleCurve (c : ℂ) (R : ℝ) : PiecewiseC1ClosedCurve :=
  PiecewiseC1ClosedCurve.of (circleMap c R)
    (IsPiecewiseC1On.of_contDiffOn (contDiff_circleMap c R).contDiffOn)
    (by simpa using (periodic_circleMap c R 0).symm)

/-- The bundled circle starts at `0`. -/
@[simp]
theorem circleCurve_a (c : ℂ) (R : ℝ) : (circleCurve c R).a = 0 := by
  rw [circleCurve, PiecewiseC1ClosedCurve.of_a]

/-- The bundled circle ends at `2π`. -/
@[simp]
theorem circleCurve_b (c : ℂ) (R : ℝ) : (circleCurve c R).b = 2 * π := by
  rw [circleCurve, PiecewiseC1ClosedCurve.of_b]

/-- On its parameter interval, the bundled circle agrees with `circleMap c R`. -/
@[simp]
theorem circleCurve_apply {c : ℂ} {R t : ℝ} (ht : t ∈ uIcc 0 (2 * π)) :
    circleCurve c R t = circleMap c R t := by
  rw [circleCurve]
  exact PiecewiseC1ClosedCurve.of_apply _ _ _ ht

/-- The counterclockwise circle `circleMap c R` on `[0, 2π]` as a one-generator contour cycle. -/
def circleCycle (c : ℂ) (R : ℝ) : Cycle :=
  FreeAddCommGroup.of (circleCurve c R)

/-- Defining formula for `TauCeti.Contour.circleCycle`. -/
theorem circleCycle_def (c : ℂ) (R : ℝ) :
    circleCycle c R = FreeAddCommGroup.of (circleCurve c R) :=
  (rfl)

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

/-- For `R ≥ 0`, the trace-zero `windingWeight` of `circleCycle c R` is the indicator of
`ball c R`. -/
theorem windingWeight_circleCycle (c : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    (circleCycle c R).windingWeight = (ball c R).indicator 1 := by
  have htr : trace (circleCycle c R) = sphere c R := by
    rw [trace_circleCycle, abs_of_nonneg hR]
  ext z
  rcases lt_trichotomy (dist z c) R with hlt | heq | hgt
  · rw [windingWeight_eq_of_notMem _ (by rw [htr, mem_sphere]; exact hlt.ne),
      windingNumber_circleCycle_eq_one_of_dist_lt hlt,
      indicator_of_mem (mem_ball.mpr hlt), Pi.one_apply, Complex.one_re]
  · rw [windingWeight_eq_zero_of_mem _ (by rw [htr, mem_sphere]; exact heq),
      indicator_of_notMem (by simp [mem_ball, heq])]
  · rw [windingWeight_eq_of_notMem _ (by rw [htr, mem_sphere]; exact hgt.ne'),
      windingNumber_circleCycle_eq_zero_of_lt_dist hR hgt,
      indicator_of_notMem (by simp [mem_ball, hgt.le]), Complex.zero_re]

end Cycle

end TauCeti.Contour
