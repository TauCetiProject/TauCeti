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
determinant in the change of variables formula for maps of the plane `ℝ × ℝ`.

Consequently `A` multiplies the wedge product of two linear forms `κ` and `α` on `R × R` by its
determinant: `κ (A e₁) α (A e₂) - κ (A e₂) α (A e₁) = det A (κ e₁ α e₂ - κ e₂ α e₁)`. This is the
transformation rule of a two-form on the plane under pullback.

## Main results

* `LinearMap.det_finTwoProd`: the determinant of an endomorphism of `R × R`.
* `LinearMap.det_mul_wedge_finTwoProd`: an endomorphism of `R × R` multiplies the wedge product
  of two linear forms by its determinant.
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

/-- An endomorphism `A` of `R × R` multiplies the wedge product `κ ∧ α` of two linear forms on
`R × R`, evaluated on the standard basis vectors `(1, 0)` and `(0, 1)`, by its determinant. -/
theorem det_mul_wedge_finTwoProd (A : (R × R) →ₗ[R] R × R) (κ α : (R × R) →ₗ[R] R) :
    LinearMap.det A * (κ (1, 0) * α (0, 1) - κ (0, 1) * α (1, 0)) =
      κ (A (1, 0)) * α (A (0, 1)) - κ (A (0, 1)) * α (A (1, 0)) := by
  have h (φ : (R × R) →ₗ[R] R) (e : R × R) : φ e = e.1 * φ (1, 0) + e.2 * φ (0, 1) := by
    have he : e = e.1 • ((1, 0) : R × R) + e.2 • ((0, 1) : R × R) := by ext <;> simp
    conv_lhs => rw [he]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [det_finTwoProd, h κ (A (1, 0)), h κ (A (0, 1)), h α (A (1, 0)), h α (A (0, 1))]
  ring

end LinearMap
