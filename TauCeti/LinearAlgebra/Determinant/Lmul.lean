/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant

/-!
# Determinants of coordinatewise multiplication

Multiplication by `f : ι → R` on the free module `ι → R` acts diagonally in the standard basis,
so its determinant is the product `∏ i, f i` of the coordinates of `f`
(`LinearMap.det_lmul_pi`). This is the finite-product analogue of Mathlib's
`LinearMap.det_mulLeft` for multiplication on `R`.

## Main results

* `LinearMap.det_lmul_pi`: `det (x ↦ f * x) = ∏ i, f i` on `ι → R`.
-/

public section

namespace LinearMap

variable {R ι : Type*} [CommRing R] [Fintype ι]

/-- The determinant of multiplication by `f` on `ι → R` is `∏ i, f i`. -/
theorem det_lmul_pi (f : ι → R) : LinearMap.det (Algebra.lmul R (ι → R) f) = ∏ i, f i := by
  classical
  have : Algebra.lmul R (ι → R) f = Matrix.toLin' (Matrix.diagonal f) := by
    ext v i
    simp [Matrix.mulVec_diagonal]
  rw [this, LinearMap.det_toLin', Matrix.det_diagonal]

end LinearMap
