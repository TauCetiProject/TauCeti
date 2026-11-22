/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# Rotations of the plane and derivatives along the unit circle

The rotation `t ↦ e^{it} z` of a point `z` of the plane preserves its norm and has velocity
`i e^{it} z`. A function `φ` on the plane has a *derivative along the rotations* at a point `w` of
the unit circle when `t ↦ φ (e^{it} w)` is differentiable at `t = 0`; this is the derivative of the
boundary values of `φ` in the angle. Such a derivative at every point of the circle gives the
derivative of `t ↦ φ (e^{it} w)` at every `t`, and a bound `M` on it makes `φ` `2 M`-Lipschitz on
the circle, since the arc between two points is at most `π / 2` times their distance
(`Complex.abs_arg_le_pi_div_two_mul_norm_sub_one`).

## Main declarations

* `TauCeti.norm_exp_I_mul_mul`: rotations preserve the norm.
* `TauCeti.hasDerivAt_exp_I_mul_mul`: the rotation `t ↦ e^{it} z` has velocity `i e^{it} z`.
* `TauCeti.hasDerivAt_comp_exp_I_mul_mul`: a derivative along the rotations at every point of the
  circle gives the derivative of `t ↦ φ (e^{it} w)` at every `t`.
* `TauCeti.lipschitzOnWith_sphere_of_hasDerivAt_exp_mul`: a derivative along the rotations bounded
  by `M` makes a function `2 M`-Lipschitz on the circle.
-/

public section

namespace TauCeti

open Complex Metric Set
open scoped NNReal Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Rotations preserve the norm: `‖e^{it} z‖ = ‖z‖`. -/
theorem norm_exp_I_mul_mul (t : ℝ) (z : ℂ) : ‖exp (I * t) * z‖ = ‖z‖ := by
  rw [norm_mul, norm_exp_I_mul_ofReal, one_mul]

/-- The rotation `t ↦ e^{it} z` has velocity `i e^{it} z`. -/
theorem hasDerivAt_exp_I_mul_mul (z : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ exp (I * t) * z) (I * (exp (I * t) * z)) t := by
  convert (((ofRealCLM.hasDerivAt (x := t)).const_mul I).cexp).mul_const z using 1
  · simp only [ofRealCLM_apply]
  · simp only [ofRealCLM_apply, ofReal_one, mul_one]
    ring

/-- A derivative along the rotations at every point of the unit circle gives the derivative of
`t ↦ φ (e^{it} w)` at every `t`, not only at `t = 0`. -/
theorem hasDerivAt_comp_exp_I_mul_mul {φ v : ℂ → E}
    (hv : ∀ w ∈ sphere (0 : ℂ) 1, HasDerivAt (fun t : ℝ ↦ φ (exp (I * t) * w)) (v w) 0)
    {w : ℂ} (hw : w ∈ sphere (0 : ℂ) 1) (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ φ (exp (I * t) * w)) (v (exp (I * t) * w)) t := by
  have h := HasDerivAt.comp_sub_const t t (by
    rw [sub_self]
    exact hv (exp (I * t) * w)
      (by rw [mem_sphere_zero_iff_norm, norm_exp_I_mul_mul, mem_sphere_zero_iff_norm.1 hw]))
  convert h using 2 with x
  rw [← mul_assoc, ← exp_add]
  push_cast
  rw [show I * (x - t) + I * t = I * x by ring]

/-- **A derivative along the rotations bounds the oscillation on the circle.** If at every point
`w` of the unit circle `t ↦ φ (e^{it} w)` has derivative `v w` at `t = 0`, and `‖v‖ ≤ M` on the
circle, then `φ` is `2 M`-Lipschitz on the circle: the arc between two points is at most twice
their distance. -/
theorem lipschitzOnWith_sphere_of_hasDerivAt_exp_mul {φ v : ℂ → E} {M : ℝ≥0}
    (hv : ∀ w ∈ sphere (0 : ℂ) 1, HasDerivAt (fun t : ℝ ↦ φ (exp (I * t) * w)) (v w) 0)
    (hM : ∀ w ∈ sphere (0 : ℂ) 1, ‖v w‖ ≤ M) : LipschitzOnWith (2 * M) φ (sphere 0 1) := by
  refine LipschitzOnWith.of_dist_le_mul fun w hw w' hw' ↦ ?_
  have hw1 := mem_sphere_zero_iff_norm.1 hw
  have hw1' := mem_sphere_zero_iff_norm.1 hw'
  -- Write `w = e^{is} w'` with `|s| ≤ π`.
  set s := arg (w / w')
  have hws : exp (I * s) * w' = w := by
    have h := norm_mul_exp_arg_mul_I (w / w')
    rw [norm_div, hw1, hw1', div_one, ofReal_one, one_mul] at h
    rw [mul_comm I, h, div_mul_cancel₀ _ (norm_ne_zero_iff.1 (by rw [hw1']; exact one_ne_zero))]
  have hmv := convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t : ℝ ↦ φ (exp (I * t) * w'))
    (fun t _ ↦ (hasDerivAt_comp_exp_I_mul_mul hv hw' t).hasDerivWithinAt)
    (fun t _ ↦ hM _ (by rw [mem_sphere_zero_iff_norm, norm_exp_I_mul_mul, hw1']))
    (mem_univ 0) (mem_univ s)
  simp only [ofReal_zero, mul_zero, exp_zero, one_mul, hws, sub_zero, Real.norm_eq_abs] at hmv
  have hchord : |s| ≤ 2 * dist w w' := by
    have h := abs_arg_le_pi_div_two_mul_norm_sub_one (z := w / w')
      (by rw [norm_div, hw1, hw1', div_one])
    rw [div_sub_one (norm_ne_zero_iff.1 (by rw [hw1']; exact one_ne_zero)), norm_div, hw1',
      div_one, ← dist_eq_norm] at h
    exact h.trans (by gcongr; linarith [Real.pi_le_four])
  rw [dist_eq_norm]
  calc ‖φ w - φ w'‖ ≤ M * |s| := hmv
    _ ≤ M * (2 * dist w w') := by gcongr
    _ = ((2 * M : ℝ≥0) : ℝ) * dist w w' := by push_cast; ring

end TauCeti
