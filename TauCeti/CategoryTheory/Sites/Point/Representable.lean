/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Fibres of representable sheaves at a point of a site

Let `Φ` be a point of a site `(C, J)` whose topology is subcanonical, so that every object `X`
represents a sheaf `J.yoneda.obj X`. The fibre (stalk) at `Φ` of this sheaf is the value
`Φ.fiber.obj X` of the fibre functor of `Φ`, naturally in `X`
(`CategoryTheory.GrothendieckTopology.Point.yonedaCompSheafFiberIso`). An element `x` of
`Φ.fiber.obj X` corresponds to the germ at `(X, x)` of the tautological section `𝟙 X`
(`CategoryTheory.GrothendieckTopology.Point.yonedaCompSheafFiberIso_inv_app_apply`).

This is the sheaf version of Mathlib's presheaf statement
`CategoryTheory.GrothendieckTopology.Point.shrinkYonedaCompPresheafFiberIso`, from which it is
deduced. For instance, on the small étale site of a scheme, the stalk at a geometric point of the
sheaf represented by an étale scheme is its set of lifts of the geometric point.

## References

* A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IV, §6.
-/

public section

universe v u

open CategoryTheory Opposite

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [J.Subcanonical]
  (Φ : J.Point.{v})

/-- The fibre at a point `Φ` of the sheaf represented by `X` is `Φ.fiber.obj X`, naturally in
`X`. -/
noncomputable def yonedaCompSheafFiberIso : J.yoneda ⋙ Φ.sheafFiber ≅ Φ.fiber :=
  Functor.isoWhiskerLeft J.yoneda Φ.sheafToPresheafCompPresheafFiberIso.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight J.yonedaCompSheafToPresheaf _ ≪≫
    Functor.isoWhiskerRight shrinkYonedaIsoYoneda.symm _ ≪≫
    Φ.shrinkYonedaCompPresheafFiberIso

/-- An element `x` of `Φ.fiber.obj X` corresponds to the germ at `(X, x)` of the tautological
section `𝟙 X` of the sheaf represented by `X`. -/
theorem yonedaCompSheafFiberIso_inv_app_apply (X : C) (x : Φ.fiber.obj X) :
    Φ.yonedaCompSheafFiberIso.inv.app X x =
      Φ.toPresheafFiber X x (J.yoneda.obj X).obj (𝟙 X) := by
  -- `sheafToPresheafCompPresheafFiberIso` is `Iso.refl`, so its components are identities.
  have h (F : Sheaf J (Type v)) (y) : Φ.sheafToPresheafCompPresheafFiberIso.hom.app F y = y := rfl
  simp only [yonedaCompSheafFiberIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, types_comp_apply, h,
    shrinkYonedaCompPresheafFiberIso_inv_app_toPresheafFiber, toPresheafFiber_naturality_apply]
  simp [shrinkYonedaIsoYoneda, yonedaCompSheafToPresheaf]
  -- The two sides differ only in implicit arguments, where `(J.yoneda.obj X).obj` appears
  -- in place of `yoneda.obj X`.
  rfl

end CategoryTheory.GrothendieckTopology.Point
