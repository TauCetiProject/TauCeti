/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Basic
public import TauCeti.Analysis.PDE.Vortex.GaugeFixed
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Gauge covariance of the plane-vortex deformation operators

The derivative of the charge-one gauge action fixes the connection variation and multiplies
its section variation by the circle-valued gauge. The same orthogonal action applies to the
target of the gauge-fixed operator: its gauge and curvature rows are fixed, and its complex
row is multiplied by the gauge.

This file constructs that action and proves that it intertwines both the gauge-fixed
linearization and its formal adjoint, at arbitrary fields. The identities are local and
require only differentiability of the gauge at the point in question. In particular they
apply to changes of end trivialization without requiring a globally framed gauge, or even
a vortex equation for the background. Pointwise norms and kernels are preserved. No claim
about boundedness on higher Sobolev spaces follows from the pointwise isometry alone.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Birkhäuser, 1980, Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex
open scoped ContDiff

/-- The linear part of a charge-one gauge transformation. On variations it fixes the
connection and rotates the section; on the gauge-fixed target it fixes the two real rows
and rotates the complex row. -/
def gaugeLinearAction (u : ℂ → Circle) :
    Module.End ℝ (ℂ → EuclideanSpace ℝ (Fin 4)) where
  toFun y z := !₂[y z 0, y z 1,
    (u z : ℂ).re * y z 2 - (u z : ℂ).im * y z 3,
    (u z : ℂ).im * y z 2 + (u z : ℂ).re * y z 3]
  map_add' y v := by
    ext z i
    fin_cases i <;> simp <;> ring
  map_smul' c y := by
    ext z i
    fin_cases i <;> simp <;> ring

/-- Coordinate formula for the linear gauge action. -/
theorem gaugeLinearAction_apply (u : ℂ → Circle) (y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    gaugeLinearAction u y z = !₂[y z 0, y z 1,
      (u z : ℂ).re * y z 2 - (u z : ℂ).im * y z 3,
      (u z : ℂ).im * y z 2 + (u z : ℂ).re * y z 3] := (rfl)

@[simp]
theorem gaugeLinearAction_one (y : ℂ → EuclideanSpace ℝ (Fin 4)) :
    gaugeLinearAction 1 y = y := by
  ext z i
  fin_cases i <;> simp [gaugeLinearAction_apply]

/-- Successive linear gauge actions multiply their gauges. No regularity is needed. -/
theorem gaugeLinearAction_mul (u v : ℂ → Circle) (y : ℂ → EuclideanSpace ℝ (Fin 4)) :
    gaugeLinearAction (u * v) y = gaugeLinearAction u (gaugeLinearAction v y) := by
  ext z i
  fin_cases i <;> simp [gaugeLinearAction_apply, mul_re, mul_im] <;> ring

/-- The inverse gauge undoes the linear action. -/
@[simp]
theorem gaugeLinearAction_inv_gaugeLinearAction (u : ℂ → Circle)
    (y : ℂ → EuclideanSpace ℝ (Fin 4)) :
    gaugeLinearAction u⁻¹ (gaugeLinearAction u y) = y := by
  rw [← gaugeLinearAction_mul, inv_mul_cancel, gaugeLinearAction_one]

/-- The linear action also undoes the inverse gauge. -/
@[simp]
theorem gaugeLinearAction_gaugeLinearAction_inv (u : ℂ → Circle)
    (y : ℂ → EuclideanSpace ℝ (Fin 4)) :
    gaugeLinearAction u (gaugeLinearAction u⁻¹ y) = y := by
  rw [← gaugeLinearAction_mul, mul_inv_cancel, gaugeLinearAction_one]

/-- Gauge action on differences of fields is its linear action on the difference. -/
theorem gaugeTransform_sub (u : ℂ → Circle) (x y : ℂ → EuclideanSpace ℝ (Fin 4)) :
    gaugeTransform u x - gaugeTransform u y = gaugeLinearAction u (x - y) := by
  ext z i
  fin_cases i <;> simp [gaugeTransform_apply, gaugeLinearAction_apply] <;> ring

/-- The affine gauge action transports every increment by its linear part. -/
theorem gaugeTransform_add (u : ℂ → Circle) (x y : ℂ → EuclideanSpace ℝ (Fin 4)) :
    gaugeTransform u (x + y) = gaugeTransform u x + gaugeLinearAction u y := by
  ext z i
  fin_cases i <;> simp [gaugeTransform_apply, gaugeLinearAction_apply] <;> ring

/-- The linear action is the derivative of the actual gauge action in every field direction. -/
theorem hasDerivAt_gaugeTransform_add_smul (u : ℂ → Circle)
    (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    HasDerivAt (fun t : ℝ ↦ gaugeTransform u (x + t • y) z)
      (gaugeLinearAction u y z) 0 := by
  simp_rw [gaugeTransform_add, map_smul, Pi.add_apply, Pi.smul_apply]
  simpa only [id_eq, one_smul] using
    (((hasDerivAt_id (0 : ℝ)).smul_const (gaugeLinearAction u y z)).const_add
      (gaugeTransform u x z))

/-- The linear gauge action is a pointwise isometry for the coefficient metrics of both
the field variations and the gauge-fixed target. -/
@[simp]
theorem norm_gaugeLinearAction (u : ℂ → Circle) (y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    ‖gaugeLinearAction u y z‖ = ‖y z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hn := Circle.normSq_coe (u z)
  simp only [Complex.normSq_apply] at hn
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four, gaugeLinearAction_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (y z 2 ^ 2 + y z 3 ^ 2) * hn

/-- Pointwise vanishing is preserved in both directions. -/
@[simp]
theorem gaugeLinearAction_eq_zero_iff (u : ℂ → Circle)
    (y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    gaugeLinearAction u y z = 0 ↔ y z = 0 := by
  rw [← norm_eq_zero, norm_gaugeLinearAction, norm_eq_zero]

/-- Smooth gauges preserve the regularity of variations, without differentiating a
connection increment. -/
theorem contDiff_gaugeLinearAction {n : WithTop ℕ∞} {u : ℂ → Circle}
    (hu : ContDiff ℝ n (fun z ↦ (u z : ℂ))) {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : ContDiff ℝ n y) : ContDiff ℝ n (gaugeLinearAction u y) := by
  have hr := reCLM.contDiff.comp hu
  have hi := imCLM.contDiff.comp hu
  have hc (i : Fin 4) : ContDiff ℝ n (fun z ↦ y z i) := (contDiff_piLp _).mp hy i
  apply (contDiff_piLp _).mpr
  intro i
  fin_cases i <;> simp only [gaugeLinearAction_apply, PiLp.toLp_apply]
  · exact hc 0
  · exact hc 1
  · exact (hr.mul (hc 2)).sub (hi.mul (hc 3))
  · exact (hi.mul (hc 2)).add (hr.mul (hc 3))

/-- The derivative of the real part of a circle-valued gauge in terms of its logarithmic
one-form. This is valid locally and does not choose a phase. -/
private theorem fderiv_re_coe_gauge {u : ℂ → Circle} {z : ℂ}
    (hu : DifferentiableAt ℝ (fun w ↦ (u w : ℂ)) z) (v : ℂ) :
    fderiv ℝ (fun w ↦ (u w : ℂ).re) z v = -(u z : ℂ).im * gaugeForm u z v := by
  have h := reCLM.hasFDerivAt.comp z hu.hasFDerivAt
  have heq : fderiv ℝ (fun w ↦ (u w : ℂ).re) z =
      reCLM ∘L fderiv ℝ (fun w ↦ (u w : ℂ)) z := by
    simpa only [Function.comp_def, Complex.reCLM_apply] using h.fderiv
  rw [heq]
  simpa using congrArg Complex.re (fderiv_coe_eq_mul_gaugeForm hu v)

private theorem fderiv_im_coe_gauge {u : ℂ → Circle} {z : ℂ}
    (hu : DifferentiableAt ℝ (fun w ↦ (u w : ℂ)) z) (v : ℂ) :
    fderiv ℝ (fun w ↦ (u w : ℂ).im) z v = (u z : ℂ).re * gaugeForm u z v := by
  have h := imCLM.hasFDerivAt.comp z hu.hasFDerivAt
  have heq : fderiv ℝ (fun w ↦ (u w : ℂ).im) z =
      imCLM ∘L fderiv ℝ (fun w ↦ (u w : ℂ)) z := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using h.fderiv
  rw [heq]
  simpa using congrArg Complex.im (fderiv_coe_eq_mul_gaugeForm hu v)

/-- The gauge-fixing row is unchanged under gauge transformation of the background and
linear gauge transformation of the variation. No differentiability is needed. -/
theorem gaugeAdjoint_gaugeTransform (u : ℂ → Circle)
    (x y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    gaugeAdjoint (gaugeTransform u x) (gaugeLinearAction u y) z = gaugeAdjoint x y z := by
  have hn := Circle.normSq_coe (u z)
  simp only [Complex.normSq_apply] at hn
  simp [gaugeAdjoint_def, gaugeTransform_apply, gaugeLinearAction_apply]
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
  have hr : DifferentiableAt ℝ (fun w ↦ (u w : ℂ).re) z :=
    reCLM.differentiableAt.comp z hu
  have hi : DifferentiableAt ℝ (fun w ↦ (u w : ℂ).im) z :=
    imCLM.differentiableAt.comp z hu
  have hn := Circle.normSq_coe (u z)
  simp only [Complex.normSq_apply] at hn
  ext i
  fin_cases i
  · simpa [gaugeLinearAction_apply, -gaugeAdjoint_def] using
      gaugeAdjoint_gaugeTransform u x y z
  all_goals
    simp [gaugeLinearAction_apply, gaugeTransform_apply,
      fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul, hr, hi, hp, hq,
      fderiv_re_coe_gauge hu, fderiv_im_coe_gauge hu, -gaugeForm_apply]
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
  have hr : DifferentiableAt ℝ (fun w ↦ (u w : ℂ).re) z :=
    reCLM.differentiableAt.comp z hu
  have hi : DifferentiableAt ℝ (fun w ↦ (u w : ℂ).im) z :=
    imCLM.differentiableAt.comp z hu
  have hn := Circle.normSq_coe (u z)
  simp only [Complex.normSq_apply] at hn
  ext i
  fin_cases i <;>
    simp [gaugeLinearAction_apply, gaugeTransform_apply,
      fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul, hr, hi, hp, hq,
      fderiv_re_coe_gauge hu, fderiv_im_coe_gauge hu, -gaugeForm_apply]
  · linear_combination (x z 2 * η z 3 - x z 3 * η z 2) * hn
  · linear_combination (-x z 2 * η z 2 - x z 3 * η z 3) * hn
  · ring
  · ring

end TauCeti.Vortex
