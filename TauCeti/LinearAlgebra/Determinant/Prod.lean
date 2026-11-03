/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant

/-!
# The determinant of an endomorphism of `R × R`

An endomorphism `A` of `R × R` is determined by the images `A (1, 0)` and `A (0, 1)` of the
standard basis vectors, and its determinant is the `2 × 2` determinant of these two columns. This
is `Matrix.det_fin_two` read through the basis `Module.Basis.finTwoProd R`. It is the Jacobian
determinant in the change of variables formula for maps of the plane `ℝ × ℝ`. Accordingly the
wedge of two linear functionals scales by the determinant (`LinearMap.apply_mul_apply_sub_det`),
which is how two-forms on the plane change under a change of coordinates.
-/

public section

namespace LinearMap

variable {R : Type*} [CommRing R]

/-- The determinant of an endomorphism of `R × R` in terms of the images `A (1, 0)` and
`A (0, 1)` of the standard basis vectors. -/
theorem det_finTwoProd (A : (R × R) →ₗ[R] R × R) :
    LinearMap.det A = (A (1, 0)).1 * (A (0, 1)).2 - (A (1, 0)).2 * (A (0, 1)).1 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd R), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Module.Basis.finTwoProd_zero, Module.Basis.finTwoProd_one]
  ring

/-- The wedge `a ∧ b` of two linear functionals on `R × R`, evaluated on the images of the
standard basis vectors under an endomorphism `A`, is `det A` times its value on the standard
basis vectors. -/
theorem apply_mul_apply_sub_det (A : (R × R) →ₗ[R] R × R) (a b : (R × R) →ₗ[R] R) :
    a (A (1, 0)) * b (A (0, 1)) - a (A (0, 1)) * b (A (1, 0)) =
      LinearMap.det A * (a (1, 0) * b (0, 1) - a (0, 1) * b (1, 0)) := by
  have h (c : (R × R) →ₗ[R] R) (w : R × R) : c w = w.1 * c (1, 0) + w.2 * c (0, 1) := by
    conv_lhs => rw [show w = w.1 • ((1 : R), (0 : R)) + w.2 • ((0 : R), (1 : R)) by ext <;> simp]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [h a (A (1, 0)), h b (A (0, 1)), h a (A (0, 1)), h b (A (1, 0)), det_finTwoProd]
  ring

end LinearMap
