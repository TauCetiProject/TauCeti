/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import TauCeti.LinearAlgebra.Determinant.Complex

/-!
# Real coordinates of the complex plane

The real linear coordinate interchange supplies its underlying homeomorphism and has
determinant `-1`, recording the reversal of orientation.
-/

public section

namespace Complex

/-- The real continuous linear equivalence interchanging real and imaginary coordinates. -/
noncomputable def coordinateSwapCLE : ℂ ≃L[ℝ] ℂ :=
  (equivRealProdCLM.trans
    (LinearIsometryEquiv.prodComm ℝ ℝ ℝ).toContinuousLinearEquiv).trans
      equivRealProdCLM.symm

/-- Coordinate swap sends `(x,y)` to `(y,x)`. -/
@[simp]
theorem coordinateSwapCLE_apply (z : ℂ) : coordinateSwapCLE z = ⟨z.im, z.re⟩ := (rfl)

/-- Interchanging the coordinates has real determinant `-1`. -/
@[simp]
theorem det_coordinateSwapCLE : coordinateSwapCLE.toLinearEquiv.toLinearMap.det = -1 := by
  rw [LinearMap.det_complex]
  simp

/-- The homeomorphism underlying the real linear coordinate interchange. -/
noncomputable def coordinateSwap : ℂ ≃ₜ ℂ := coordinateSwapCLE.toHomeomorph

/-- Coordinate swap sends `(x,y)` to `(y,x)`. -/
@[simp]
theorem coordinateSwap_apply (z : ℂ) : coordinateSwap z = ⟨z.im, z.re⟩ := (rfl)

end Complex
