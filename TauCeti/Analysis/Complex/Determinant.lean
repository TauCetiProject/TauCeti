/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.LinearAlgebra.Complex.Determinant
import TauCeti.LinearAlgebra.Complex.Determinant

/-!
# The real determinant of a complex dilation-rotation

Multiplication by `c : ℂ`, read as a real-linear map of the plane, has determinant `‖c‖ ^ 2`
(`ContinuousLinearMap.det_restrictScalars_smulRight_one`): it is the rotation by `arg c` scaled by
`‖c‖`, and a dilation of ratio `‖c‖` multiplies area by `‖c‖ ^ 2`. It is the continuous-linear
form, at the complex line, of `LinearMap.det_restrictScalars_eq_normSq`.

The map is written as `ContinuousLinearMap.smulRight 1 c` because that is the shape in which
`HasDerivAt.hasFDerivAt` presents the Fréchet derivative of a function of one complex variable, so
this is the Jacobian determinant of a complex differentiable map of the plane.

Complex conjugation reverses orientation: as a real-linear map it has determinant `-1`
(`Complex.det_conjCLE`), so composing with it negates a real determinant
(`ContinuousLinearMap.det_conjCLE_comp`). Together with the previous formula this gives the
Jacobian `-‖c‖ ^ 2` of an antiholomorphic map `z ↦ conj (f z)` with `f' z = c`.
-/

public section

namespace ContinuousLinearMap

/-- **The Jacobian of a complex dilation-rotation.** Multiplication by `c : ℂ`, read as an
`ℝ`-linear map of the plane, has determinant `‖c‖ ^ 2`. -/
theorem det_restrictScalars_smulRight_one (c : ℂ) :
    ((smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ).det = ‖c‖ ^ 2 := by
  rw [det, coe_restrictScalars, LinearMap.det_restrictScalars_eq_normSq,
    Complex.normSq_eq_norm_sq]
  simp [smulRight_one_eq_toSpanSingleton]

/-- Complex conjugation reverses orientation: composing a real-linear map of the plane with it
negates the determinant. -/
theorem det_conjCLE_comp (A : ℂ →L[ℝ] ℂ) :
    ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp A).det = -A.det := by
  simp [det]

end ContinuousLinearMap

namespace Complex

/-- Complex conjugation, as a real-linear map of the plane, has determinant `-1`. -/
@[simp]
theorem det_conjCLE : (conjCLE : ℂ →L[ℝ] ℂ).det = -1 := by
  simp [ContinuousLinearMap.det]

end Complex
