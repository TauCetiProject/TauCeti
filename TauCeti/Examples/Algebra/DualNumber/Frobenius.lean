/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.DualNumber.Frobenius

/-!
# Nondegenerate vs perfect Frobenius pairings on `DualNumber ℤ`

Over a field every nondegenerate Frobenius functional induces a perfect multiplication pairing,
whereas over a general commutative ring nondegeneracy is strictly weaker than perfectness.
Specifically, `(2 : ℤ) • sndHom ℤ ℤ` on `DualNumber ℤ` has Gram determinant `-4 ≠ 0` in the basis
`(1, ε)`, so it is a symmetric Frobenius functional whose multiplication pairing is not perfect.
-/

public section

open DualNumber TrivSqZeroExt

namespace TauCeti

/-- On `DualNumber ℤ`, the Gram matrix of `(2 : ℤ) • sndHom ℤ ℤ` in `(1, ε)` has determinant
`-4`. -/
theorem det_toMatrix₂_compr₂_mul_two_smul_sndHom_int :
    (LinearMap.toMatrix₂ (dualNumberBasis ℤ) (dualNumberBasis ℤ)
      ((LinearMap.mul ℤ (DualNumber ℤ)).compr₂ ((2 : ℤ) • sndHom ℤ ℤ))).det = -4 := by
  rw [det_toMatrix₂_compr₂_mul_smul_sndHom]
  norm_num

/-- On `DualNumber ℤ`, `(2 : ℤ) • sndHom ℤ ℤ` is a symmetric Frobenius functional. -/
theorem isSymmetricFrobeniusFunctional_two_smul_sndHom_int :
    ((2 : ℤ) • sndHom ℤ ℤ).IsSymmetricFrobeniusFunctional :=
  isSymmetricFrobeniusFunctional_smul_sndHom ℤ fun _ hx ↦ by omega

/-- On `DualNumber ℤ`, the nondegenerate pairing induced by `(2 : ℤ) • sndHom ℤ ℤ` is not
perfect. -/
theorem not_isPerfPair_compr₂_mul_two_smul_sndHom_int :
    ¬ ((LinearMap.mul ℤ (DualNumber ℤ)).compr₂ ((2 : ℤ) • sndHom ℤ ℤ)).IsPerfPair := by
  rw [isPerfPair_compr₂_mul_smul_sndHom_iff, Int.isUnit_iff]
  omega

end TauCeti
