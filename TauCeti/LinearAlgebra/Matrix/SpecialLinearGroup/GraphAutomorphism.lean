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
* `Matrix.SpecialLinearGroup.typeAGraphAutomorphism_transvection_of_ne`: its action on every
  root subgroup.
* `Matrix.SpecialLinearGroup.typeAGraphAutomorphism_typeAGraphAutomorphism` and
  `Matrix.SpecialLinearGroup.typeAGraphAutomorphism_mul_self`: the involution equations.

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

/-- The special-linear graph automorphism sends the transvection at `ε_i - ε_j` to the
transvection at `ε_{rev j} - ε_{rev i}`, with the sign from the signed conjugator. -/
@[simp]
theorem typeAGraphAutomorphism_transvection_of_ne {i j : Fin (r + 1)}
    (hij : i ≠ j) (c : A) :
    typeAGraphAutomorphism r A (transvection hij c) =
      transvection (Fin.rev_injective.ne hij.symm)
        ((-1 : A) ^ ((i : ℕ) + (j : ℕ) + 1) * c) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [toGL_typeAGraphAutomorphism, TauCeti.toGL_transvection_eq_transvectionUnit,
    TauCeti.typeAGraphAutomorphism_transvectionUnit_of_ne,
    TauCeti.toGL_transvection_eq_transvectionUnit]

/-- The special-linear graph automorphism reverses the positive simple-root transvections without
changing their parameters. -/
theorem typeAGraphAutomorphism_transvection (i : Fin r) (c : A) :
    typeAGraphAutomorphism r A
        (transvection (Fin.castSucc_lt_succ (i := i)).ne c) =
      transvection (Fin.castSucc_lt_succ (i := i.rev)).ne c := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [toGL_typeAGraphAutomorphism, TauCeti.toGL_transvection_eq_transvectionUnit,
    TauCeti.toGL_transvection_eq_transvectionUnit]
  exact TauCeti.typeAGraphAutomorphism_transvectionUnit r i c

/-- The special-linear graph automorphism reverses the negative simple-root transvections without
changing their parameters. -/
theorem typeAGraphAutomorphism_transvection_lower (i : Fin r) (c : A) :
    typeAGraphAutomorphism r A
        (transvection (Fin.castSucc_lt_succ (i := i)).ne' c) =
      transvection (Fin.castSucc_lt_succ (i := i.rev)).ne' c := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [toGL_typeAGraphAutomorphism, TauCeti.toGL_transvection_eq_transvectionUnit,
    TauCeti.toGL_transvection_eq_transvectionUnit]
  exact TauCeti.typeAGraphAutomorphism_transvectionUnit_lower r i c

/-- Applying the special-linear type-`A` graph automorphism twice is the identity. -/
@[simp]
theorem typeAGraphAutomorphism_typeAGraphAutomorphism
    (g : Matrix.SpecialLinearGroup (Fin (r + 1)) A) :
    typeAGraphAutomorphism r A (typeAGraphAutomorphism r A g) = g :=
  (typeAGraphAutomorphism r A).left_inv g

/-- The special-linear type-`A` graph automorphism has order dividing two. -/
@[simp]
theorem typeAGraphAutomorphism_mul_self :
    typeAGraphAutomorphism r A * typeAGraphAutomorphism r A = 1 := by
  apply DFunLike.ext _ _
  intro g
  exact typeAGraphAutomorphism_typeAGraphAutomorphism r A g

end Matrix.SpecialLinearGroup
