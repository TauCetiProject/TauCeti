/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Determinant

/-!
# Real determinants on the complex plane

The real determinant of a real-linear endomorphism of the complex plane is the two-by-two
determinant of its values at `1` and `I` in the basis `(1,I)`.
-/

public section

namespace LinearMap

/-- The real determinant of a map on the complex plane, expressed in the basis `(1,I)`. -/
theorem det_complex (L : ℂ →ₗ[ℝ] ℂ) :
    L.det = (L 1).re * (L Complex.I).im - (L Complex.I).re * (L 1).im := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr]

end LinearMap
