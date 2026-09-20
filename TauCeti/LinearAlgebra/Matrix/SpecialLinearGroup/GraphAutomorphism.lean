/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.GraphAutomorphism

/-!
# The type-A graph automorphism on the special linear group

The signed reverse-inverse-transpose automorphism of `GL_{r+1}` preserves determinant one. This
file restricts it to an involutive automorphism of `SL_{r+1}`. Its matrix formula is inherited
from `TauCeti.typeAGraphAutomorphism`, so the conjugating signs still make the action on the
standard type-A pinning sign-free.

## Main declarations

* `Matrix.SpecialLinearGroup.typeAGraphAutomorphism`: signed reverse inverse transpose on
  `SL_{r+1}`.
* `Matrix.SpecialLinearGroup.toGL_typeAGraphAutomorphism`: compatibility with the ambient
  automorphism of `GL_{r+1}`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Chapter 12.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.
-/

public section

namespace Matrix.SpecialLinearGroup

universe u

variable (r : ℕ) (A : Type u) [CommRing A]

/-- Signed reverse inverse transpose preserves determinant one. -/
private theorem typeAGraphAutomorphism_det_eq_one
    (g : Matrix.SpecialLinearGroup (Fin (r + 1)) A) :
    Matrix.det
      (TauCeti.typeAGraphAutomorphism r A (Matrix.SpecialLinearGroup.toGL g) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) A) = 1 := by
  have hInv : Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.inverseTranspose
        (Matrix.SpecialLinearGroup.toGL g)) = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.GeneralLinearGroup.coe_inverseTranspose, Matrix.det_transpose]
    have hdet := congrArg Units.val
      (map_inv Matrix.GeneralLinearGroup.det
        (Matrix.SpecialLinearGroup.toGL g))
    simpa only [Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.SpecialLinearGroup.coeToGL_det, inv_one, Units.val_one] using hdet
  have h : Matrix.GeneralLinearGroup.det
      (TauCeti.typeAGraphAutomorphism r A
        (Matrix.SpecialLinearGroup.toGL g)) = 1 := by
    rw [TauCeti.typeAGraphAutomorphism_apply, map_mul, map_mul, hInv, map_inv]
    simp only [mul_one, mul_inv_cancel]
  simpa only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] using
    congrArg Units.val h

private noncomputable def typeAGraphAutomorphismToSL
    (g : Matrix.SpecialLinearGroup (Fin (r + 1)) A) :
    Matrix.SpecialLinearGroup (Fin (r + 1)) A :=
  ⟨TauCeti.typeAGraphAutomorphism r A (Matrix.SpecialLinearGroup.toGL g),
    typeAGraphAutomorphism_det_eq_one r A g⟩

private theorem toGL_typeAGraphAutomorphismToSL
    (g : Matrix.SpecialLinearGroup (Fin (r + 1)) A) :
    Matrix.SpecialLinearGroup.toGL (typeAGraphAutomorphismToSL r A g) =
      TauCeti.typeAGraphAutomorphism r A (Matrix.SpecialLinearGroup.toGL g) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change ((TauCeti.typeAGraphAutomorphism r A
    (Matrix.SpecialLinearGroup.toGL g) :
      Matrix.GeneralLinearGroup (Fin (r + 1)) A) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) A) i j = _
  rfl

/-- **The signed reverse-inverse-transpose automorphism of `SL_{r+1}`.** This is the restriction
of `TauCeti.typeAGraphAutomorphism` from the general linear group to determinant-one matrices. -/
noncomputable def typeAGraphAutomorphism :
    Matrix.SpecialLinearGroup (Fin (r + 1)) A ≃*
      Matrix.SpecialLinearGroup (Fin (r + 1)) A where
  toFun := typeAGraphAutomorphismToSL r A
  invFun := typeAGraphAutomorphismToSL r A
  left_inv g := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [toGL_typeAGraphAutomorphismToSL, toGL_typeAGraphAutomorphismToSL]
    exact TauCeti.typeAGraphAutomorphism_typeAGraphAutomorphism r
      (Matrix.SpecialLinearGroup.toGL g)
  right_inv g := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [toGL_typeAGraphAutomorphismToSL, toGL_typeAGraphAutomorphismToSL]
    exact TauCeti.typeAGraphAutomorphism_typeAGraphAutomorphism r
      (Matrix.SpecialLinearGroup.toGL g)
  map_mul' g h := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [toGL_typeAGraphAutomorphismToSL]
    rw [map_mul Matrix.SpecialLinearGroup.toGL
      (typeAGraphAutomorphismToSL r A g) (typeAGraphAutomorphismToSL r A h)]
    rw [toGL_typeAGraphAutomorphismToSL, toGL_typeAGraphAutomorphismToSL]
    rw [map_mul Matrix.SpecialLinearGroup.toGL g h]
    exact map_mul (TauCeti.typeAGraphAutomorphism r A) _ _

/-- The special-linear graph automorphism restricts the ambient general-linear graph
automorphism. -/
@[simp]
theorem toGL_typeAGraphAutomorphism
    (g : Matrix.SpecialLinearGroup (Fin (r + 1)) A) :
    Matrix.SpecialLinearGroup.toGL (typeAGraphAutomorphism r A g) =
      TauCeti.typeAGraphAutomorphism r A (Matrix.SpecialLinearGroup.toGL g) :=
  toGL_typeAGraphAutomorphismToSL r A g

end Matrix.SpecialLinearGroup
