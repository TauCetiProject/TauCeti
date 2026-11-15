/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InverseTranspose
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

/-!
# Inverse transpose on the special linear group

Over a commutative ring, the inverse-transpose operation `g ↦ (g⁻¹)ᵀ` preserves determinant one
and defines an involutive group automorphism of `SL(n, R)`. It restricts the general-linear
automorphism `Matrix.GeneralLinearGroup.inverseTranspose`, commutes with entrywise ring
homomorphisms, and carries each elementary transvection `transvection hij c` to the opposite
transvection `transvection hij.symm (-c)`.

## Main definitions

* `Matrix.SpecialLinearGroup.inverseTranspose`: the automorphism `g ↦ (g⁻¹)ᵀ` of `SL(n, R)`.

## Main results

* `Matrix.SpecialLinearGroup.inverseTranspose_apply`,
  `Matrix.SpecialLinearGroup.coe_inverseTranspose`, and
  `Matrix.SpecialLinearGroup.toGL_inverseTranspose`: compatibility with `transpose`, the underlying
  matrix, and `Matrix.GeneralLinearGroup.inverseTranspose`.
* `Matrix.SpecialLinearGroup.inverseTranspose_inverseTranspose` and
  `Matrix.SpecialLinearGroup.inverseTranspose_symm`: inverse transpose is an involution.
* `Matrix.SpecialLinearGroup.map_inverseTranspose`: naturality under ring homomorphisms.
* `Matrix.SpecialLinearGroup.inverseTranspose_transvection`: action on elementary transvections.
-/

public section

namespace Matrix.SpecialLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

private theorem toGL_inv_transpose (g : SpecialLinearGroup n R) :
    toGL ((g⁻¹).transpose) = Matrix.GeneralLinearGroup.inverseTranspose (toGL g) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_inverseTranspose, ← map_inv]
  rfl

/-- **Inverse transpose on the special linear group.** This is the involutive automorphism
`g ↦ (g⁻¹)ᵀ`, restricting `Matrix.GeneralLinearGroup.inverseTranspose` to determinant-one
matrices. -/
def inverseTranspose : SpecialLinearGroup n R ≃* SpecialLinearGroup n R where
  toFun g := (g⁻¹).transpose
  invFun g := (g⁻¹).transpose
  left_inv g := toGL_injective <| by
    rw [toGL_inv_transpose, toGL_inv_transpose,
      Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose]
  right_inv g := toGL_injective <| by
    rw [toGL_inv_transpose, toGL_inv_transpose,
      Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose]
  map_mul' g h := toGL_injective <| by
    simp only [toGL_inv_transpose, map_mul]

/-- Applying `inverseTranspose` to `g` yields `(g⁻¹).transpose`. -/
theorem inverseTranspose_apply (g : SpecialLinearGroup n R) :
    inverseTranspose g = (g⁻¹).transpose :=
  (rfl)

/-- The matrix underlying `inverseTranspose g` is `(g⁻¹)ᵀ`. -/
@[simp]
theorem coe_inverseTranspose (g : SpecialLinearGroup n R) :
    (inverseTranspose g : Matrix n n R) =
      ((g⁻¹ : SpecialLinearGroup n R) : Matrix n n R).transpose :=
  (rfl)

/-- Embedding into `GL n R` intertwines the special-linear and general-linear inverse-transpose
automorphisms. -/
@[simp]
theorem toGL_inverseTranspose (g : SpecialLinearGroup n R) :
    toGL (inverseTranspose g) = Matrix.GeneralLinearGroup.inverseTranspose (toGL g) :=
  toGL_inv_transpose g

/-- Inverse transpose on `SL(n, R)` is an involution. -/
@[simp]
theorem inverseTranspose_inverseTranspose (g : SpecialLinearGroup n R) :
    inverseTranspose (inverseTranspose g) = g :=
  inverseTranspose.left_inv g

/-- Inverse transpose on `SL(n, R)` is its own inverse automorphism. -/
@[simp]
theorem inverseTranspose_symm :
    (inverseTranspose : SpecialLinearGroup n R ≃* SpecialLinearGroup n R).symm =
      inverseTranspose :=
  (rfl)

variable {S : Type*} [CommRing S]

/-- Inverse transpose on `SL(n, R)` commutes with entrywise application of a ring homomorphism. -/
@[simp]
theorem map_inverseTranspose (f : R →+* S) (g : SpecialLinearGroup n R) :
    map f (inverseTranspose g) = inverseTranspose (map f g) := by
  ext a b
  simp only [coe_inverseTranspose, ← map_inv, map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.transpose_apply, Matrix.map_apply]

/-- Inverse transpose exchanges the indices of an elementary transvection and negates its
parameter. -/
@[simp]
theorem inverseTranspose_transvection {i j : n} (hij : i ≠ j) (c : R) :
    inverseTranspose (transvection hij c) = transvection hij.symm (-c) := by
  ext a b
  rw [coe_inverseTranspose, transvection_inv, transpose_coe_transvection]

end Matrix.SpecialLinearGroup
