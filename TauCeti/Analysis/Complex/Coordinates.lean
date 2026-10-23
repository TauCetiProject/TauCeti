/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import TauCeti.LinearAlgebra.Complex.Determinant

/-!
# Real coordinates of the complex plane

The real linear coordinate interchange is an involution with determinant `-1`, recording
the reversal of orientation.
-/

public section

namespace Complex

/-- The real continuous linear equivalence interchanging real and imaginary coordinates. -/
noncomputable def coordinateSwapCLE : ℂ ≃L[ℝ] ℂ :=
  (equivRealProdCLM.trans (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ)).trans
    equivRealProdCLM.symm

/-- Coordinate swap sends `(x,y)` to `(y,x)`. -/
@[simp]
theorem coordinateSwapCLE_apply (z : ℂ) : coordinateSwapCLE z = ⟨z.im, z.re⟩ := (rfl)

/-- Coordinate interchange is its own inverse. -/
@[simp]
theorem coordinateSwapCLE_symm : coordinateSwapCLE.symm = coordinateSwapCLE := by
  ext z
  rfl

/-- Interchanging the coordinates twice returns the original point. -/
theorem coordinateSwapCLE_coordinateSwapCLE (z : ℂ) :
    coordinateSwapCLE (coordinateSwapCLE z) = z := (rfl)

/-- Interchanging the coordinates has real determinant `-1`. -/
@[simp]
theorem det_coordinateSwapCLE : coordinateSwapCLE.toLinearEquiv.toLinearMap.det = -1 := by
  rw [LinearMap.det_complex]
  simp

/-- The determinant unit of coordinate interchange is `-1`. -/
@[simp]
theorem linearEquiv_det_coordinateSwapCLE : coordinateSwapCLE.toLinearEquiv.det = -1 := by
  simp [← Units.val_inj]

end Complex
