/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orientation
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.CrossProduct

/-!
# The volume form of `ℝ³` and the triple product

For the standard orientation of `ℝ³ = EuclideanSpace ℝ (Fin 3)`, given by its standard basis, the
oriented volume form is the triple product `vol(u, v, w) = u ⬝ (v × w)`
(`EuclideanSpace.volumeForm_basisFun_orientation_three`). This expresses volume forms built from an
orientation of `ℝ³`, such as the area form of the unit sphere, through Mathlib's cross product.
-/

public section

open Matrix WithLp

/-- The volume form of the standard orientation of `ℝ³` is the triple product:
`vol(u, v, w) = u ⬝ (v × w)`. -/
theorem EuclideanSpace.volumeForm_basisFun_orientation_three
    (u v w : EuclideanSpace ℝ (Fin 3)) :
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.volumeForm ![u, v, w] =
      ofLp u ⬝ᵥ ofLp v ⨯₃ ofLp w := by
  rw [Orientation.volumeForm_robust _ (EuclideanSpace.basisFun (Fin 3) ℝ) rfl,
    Module.Basis.det_apply, triple_product_eq_det, ← det_transpose]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Module.Basis.toMatrix_apply]
