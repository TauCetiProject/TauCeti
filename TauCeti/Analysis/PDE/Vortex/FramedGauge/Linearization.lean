/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Basic
public import TauCeti.Analysis.PDE.Vortex.GaugeFixed
import TauCeti.Analysis.Complex.Circle

/-!
# Gauge covariance of the plane-vortex deformation operators

The derivative of the charge-one gauge action fixes the connection variation and multiplies
its section variation by the circle-valued gauge. The same orthogonal action applies to the
target of the gauge-fixed operator: its gauge and curvature rows are fixed, and its complex
row is multiplied by the gauge.

The linear action, its algebraic and regularity laws, its pointwise norm and vanishing laws,
and its section-coordinate Leibniz rules are constructed in `FramedGauge.Basic`. This file
proves covariance of the infinitesimal gauge action, the gauge-fixing row, the full gauge-fixed
linearization and its formal adjoint, at arbitrary fields. The differential identities require
the gauge and the variation's two section coordinates to be differentiable at the point;
there is no regularity or vortex-equation assumption on the background. They therefore apply
to changes of end trivialization without requiring a globally framed gauge. Pointwise norms
and pointwise vanishing are preserved. No claim about boundedness on higher Sobolev spaces
follows from the pointwise isometry alone.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Birkhäuser, 1980, Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex
open scoped ContDiff

/-- The gauge-fixing row is unchanged under gauge transformation of the background and
linear gauge transformation of the variation. No differentiability is needed. -/
-- Cancel the gauge before expanding with gaugeAdjoint_def.
@[simp high]
theorem gaugeAdjoint_gaugeTransform (u : ℂ → Circle)
    (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    gaugeAdjoint (gaugeTransform u x) (gaugeLinearAction u y) z = gaugeAdjoint x y z := by
  have hn := Circle.re_sq_add_im_sq (u z)
  simp only [gaugeAdjoint_def, gaugeTransform_apply, gaugeLinearAction_apply,
    PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (x z 2 * y z 3 - x z 3 * y z 2) * hn

/-- The infinitesimal gauge action is intertwined by the linear gauge action. This law
requires no regularity of the field, gauge or infinitesimal parameter. -/
theorem gaugeDirection_gaugeTransform (u : ℂ → Circle)
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) (f : ℂ → ℝ) :
    gaugeDirection (gaugeTransform u x) f = gaugeLinearAction u (gaugeDirection x f) := by
  ext z i
  fin_cases i <;> simp [gaugeLinearAction_apply, gaugeTransform_apply] <;> ring

/-- Gauge covariance of the full gauge-fixed linearization, at arbitrary backgrounds.
Only the variation and gauge are differentiated. -/
theorem gaugeFixedOperator_gaugeTransform {u : ℂ → Circle} {z : ℂ}
    (hu : DifferentiableAt ℝ (fun w ↦ (u w : ℂ)) z)
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hp : DifferentiableAt ℝ (fun w ↦ y w 2) z)
    (hq : DifferentiableAt ℝ (fun w ↦ y w 3) z) :
    gaugeFixedOperator (gaugeTransform u x) (gaugeLinearAction u y) z =
      gaugeLinearAction u (gaugeFixedOperator x y) z := by
  have hn := Circle.re_sq_add_im_sq (u z)
  ext i
  fin_cases i
  · simpa only [Fin.reduceFinMk, gaugeFixedOperator_apply_zero, gaugeLinearAction_apply,
      PiLp.toLp_apply, Matrix.cons_val_zero] using gaugeAdjoint_gaugeTransform u x y z
  all_goals
    simp only [Fin.reduceFinMk, gaugeFixedOperator_apply_one, gaugeFixedOperator_apply_two,
      gaugeFixedOperator_apply_three, linearizedEquation_apply_zero,
      linearizedEquation_apply_one, linearizedEquation_apply_two,
      fderiv_gaugeLinearAction_apply_two hu hp hq,
      fderiv_gaugeLinearAction_apply_three hu hp hq]
    simp only [gaugeLinearAction_apply, gaugeTransform_apply, PiLp.toLp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      gaugeFixedOperator_apply_one, gaugeFixedOperator_apply_two,
      gaugeFixedOperator_apply_three, linearizedEquation_apply_zero,
      linearizedEquation_apply_one, linearizedEquation_apply_two]
  · linear_combination (x z 2 * y z 2 + x z 3 * y z 3) * hn
  · ring
  · ring

/-- Gauge covariance of the formal adjoint for the same coefficient metrics. -/
theorem gaugeFixedAdjoint_gaugeTransform {u : ℂ → Circle} {z : ℂ}
    (hu : DifferentiableAt ℝ (fun w ↦ (u w : ℂ)) z)
    (x : ℂ → EuclideanSpace ℝ (Fin 4)) {η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hp : DifferentiableAt ℝ (fun w ↦ η w 2) z)
    (hq : DifferentiableAt ℝ (fun w ↦ η w 3) z) :
    gaugeFixedAdjoint (gaugeTransform u x) (gaugeLinearAction u η) z =
      gaugeLinearAction u (gaugeFixedAdjoint x η) z := by
  have hn := Circle.re_sq_add_im_sq (u z)
  ext i
  fin_cases i <;>
    simp only [Fin.reduceFinMk, gaugeFixedAdjoint_apply_zero, gaugeFixedAdjoint_apply_one,
      gaugeFixedAdjoint_apply_two, gaugeFixedAdjoint_apply_three,
      fderiv_gaugeLinearAction_apply_two hu hp hq,
      fderiv_gaugeLinearAction_apply_three hu hp hq] <;>
    simp only [gaugeLinearAction_apply, gaugeTransform_apply, PiLp.toLp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      gaugeFixedAdjoint_apply_zero, gaugeFixedAdjoint_apply_one,
      gaugeFixedAdjoint_apply_two, gaugeFixedAdjoint_apply_three]
  · linear_combination (x z 2 * η z 3 - x z 3 * η z 2) * hn
  · linear_combination (-x z 2 * η z 2 - x z 3 * η z 3) * hn
  · ring
  · ring

end TauCeti.Vortex
