/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PlaneSeparation.Inside
public import TauCeti.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# From almost-everywhere disk equality to a circular Jordan curve

The inside `filledHull C \ C` of a planar Jordan curve is regular open: its closure is the
filled hull, whose interior is the inside again. Consequently, if it agrees almost everywhere
with an open disk, it is literally that disk, and its frontier, the original curve, is literally
the corresponding circle. This upgrades measure-theoretic ball rigidity to point-set rigidity
for Jordan curves, without imposing smoothness or even rectifiability on the curve.

The results hold for any measure positive on nonempty open sets, in particular planar Lebesgue
measure. No nullity assumption on the curve is needed. The converse is also included: a circular
trace has exactly the open disk as its inside, hence agrees with it almost everywhere.

## Main results

* `TauCeti.IsJordanCurve.filledHull_sdiff_eq_ball_of_ae_eq`: a.e. disk equality of a Jordan
  inside implies literal disk equality.
* `TauCeti.IsJordanCurve.filledHull_sdiff_ae_eq_ball_iff_eq_sphere`: a Jordan inside agrees a.e.
  with a positive-radius disk exactly when its trace is the corresponding circle.
-/

public section

open MeasureTheory Metric Set

namespace TauCeti

variable {C : Set ℂ} {μ : Measure ℂ} [μ.IsOpenPosMeasure] {c : ℂ} {r : ℝ}

/-- If the inside of a Jordan curve agrees almost everywhere with a positive-radius disk, then
it equals that disk as a set. The measure need only be positive on nonempty open sets. -/
theorem IsJordanCurve.filledHull_sdiff_eq_ball_of_ae_eq (hC : IsJordanCurve C) (hr : 0 < r)
    (h : filledHull C \ C =ᵐ[μ] ball c r) : filledHull C \ C = ball c r := by
  apply eq_of_ae_eq_of_interior_closure_eq _ _ h
  · rw [hC.closure_filledHull_sdiff, hC.interior_filledHull]
  · rw [closure_ball c hr.ne', interior_closedBall c hr.ne']

/-- A Jordan curve whose inside agrees almost everywhere with a disk is exactly the bounding
circle, not merely almost everywhere equal to it. -/
theorem IsJordanCurve.eq_sphere_of_filledHull_sdiff_ae_eq_ball (hC : IsJordanCurve C)
    (hr : 0 < r) (h : filledHull C \ C =ᵐ[μ] ball c r) : C = sphere c r := by
  rw [← hC.frontier_filledHull_sdiff, hC.filledHull_sdiff_eq_ball_of_ae_eq hr h,
    frontier_ball c hr.ne']

/-- Almost-everywhere equality of a Jordan inside with a positive-radius disk is equivalent
to literal equality of the trace with the corresponding circle. This bridges measure-theoretic
ball rigidity and geometric circle rigidity. -/
theorem IsJordanCurve.filledHull_sdiff_ae_eq_ball_iff_eq_sphere (hC : IsJordanCurve C)
    (hr : 0 < r) : (filledHull C \ C =ᵐ[μ] ball c r) ↔ C = sphere c r := by
  refine ⟨hC.eq_sphere_of_filledHull_sdiff_ae_eq_ball hr, fun h ↦ ?_⟩
  rw [h, filledHull_sphere c hr.le, closedBall_sdiff_sphere]

end TauCeti
