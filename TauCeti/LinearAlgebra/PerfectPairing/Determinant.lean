/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
import TauCeti.LinearAlgebra.PerfectPairing.Basis

/-!
# The determinant pairing of a basis of rank two

For a basis `b` of a module `M` of rank two over a commutative ring `R`, the determinant
`(x, y) ↦ det_b [x, y]` of a pair of vectors is a bilinear pairing of `M` with itself
(`Module.Basis.detPairing`). In the coordinates `x = x₀ b₀ + x₁ b₁` it is `x₀ y₁ - x₁ y₀`. It is
alternating and its Gram matrix in `b` is `[[0, 1], [-1, 0]]`, of determinant one, so it is a
perfect pairing over every commutative ring. Another basis `b'` gives the pairing multiplied by the
unit `det_b' b`.

For the lattice `Λ = H₁(C; ℤ)` of a closed oriented surface `C` of genus one, written in a basis
positive for the orientation, this is the intersection pairing of `C`.

## Main results

* `Module.Basis.detPairing_apply_eq_det`: the pairing is `(x, y) ↦ det_b [x, y]`.
* `Module.Basis.detPairing_self`, `Module.Basis.flip_detPairing`: it is alternating, and
  skew-symmetric.
* `Module.Basis.isPerfPair_detPairing`: it is a perfect pairing.
* `Module.Basis.detPairing_eq_smul`: changing the basis multiplies it by a determinant.
-/

public section

namespace Module.Basis

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The **determinant pairing** of a basis `b` of rank two: the bilinear pairing
`(x, y) ↦ x₀ y₁ - x₁ y₀` in the coordinates of `b`, which is `det_b [x, y]`
(`Module.Basis.detPairing_apply_eq_det`). For a positive basis of `H₁` of an oriented torus it is
the intersection pairing. -/
noncomputable def detPairing (b : Basis (Fin 2) R M) : M →ₗ[R] M →ₗ[R] R :=
  (b.coord 0).smulRight (b.coord 1) - (b.coord 1).smulRight (b.coord 0)

theorem detPairing_apply (b : Basis (Fin 2) R M) (x y : M) :
    b.detPairing x y = b.repr x 0 * b.repr y 1 - b.repr x 1 * b.repr y 0 := by
  simp [detPairing]

/-- The determinant pairing of `b` is the determinant in `b` of the pair of vectors. -/
theorem detPairing_apply_eq_det (b : Basis (Fin 2) R M) (x y : M) :
    b.detPairing x y = b.det ![x, y] := by
  rw [detPairing_apply, det_apply, Matrix.det_fin_two]
  simp [toMatrix_apply, mul_comm]

@[simp]
theorem detPairing_self (b : Basis (Fin 2) R M) (x : M) : b.detPairing x x = 0 := by
  rw [detPairing_apply, mul_comm, sub_self]

theorem flip_detPairing (b : Basis (Fin 2) R M) : b.detPairing.flip = -b.detPairing := by
  ext x y
  simp only [LinearMap.flip_apply, LinearMap.neg_apply, detPairing_apply]
  ring

/-- **The determinant pairing of a basis of rank two is a perfect pairing**: its Gram matrix
`[[0, 1], [-1, 0]]` has determinant one. -/
instance isPerfPair_detPairing (b : Basis (Fin 2) R M) : b.detPairing.IsPerfPair := by
  refine isPerfPair_of_isUnit_det b b _ ?_
  rw [Matrix.det_fin_two]
  simp [LinearMap.toMatrix₂_apply, detPairing_apply]

/-- **Change of basis.** The determinant pairing of a basis `b'` is that of `b` multiplied by the
determinant of `b` in `b'`, a unit of `R`. -/
theorem detPairing_eq_smul (b b' : Basis (Fin 2) R M) :
    b'.detPairing = b'.det b • b.detPairing := by
  ext x y
  rw [LinearMap.smul_apply, LinearMap.smul_apply, detPairing_apply_eq_det,
    detPairing_apply_eq_det]
  conv_lhs => rw [b'.det.eq_smul_basis_det b]
  simp

end Module.Basis
