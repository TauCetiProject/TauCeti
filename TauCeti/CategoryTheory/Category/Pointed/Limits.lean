/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Pointed
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Over

/-!
# Limits and colimits of pointed types

We identify `Pointed` with the category of types under the one-point type, so that `Pointed` has
all limits and colimits.

## Main definitions

* `Pointed.equivUnderPUnit`: the equivalence of `Pointed` with types under `PUnit`.
* The instances `HasLimitsOfSize.{w, w} Pointed.{u}` and `HasColimitsOfSize.{w, w} Pointed.{u}`
  whenever `UnivLE.{w, u}`.
-/

public section

universe w u

open CategoryTheory Limits

namespace Pointed

/-- Pointed types are the same as types under the one-point type: a pointed type `X`
corresponds to the map `PUnit → X` picking out its basepoint.

The body is exposed so that the generated `simps` lemmas, which identify the underlying types
and basepoints on both sides, can be stated and proved by `rfl`, and so that the statement of
`equivUnderPUnit_functor_map_right_hom_apply` typechecks. -/
@[expose, simps! functor_obj_right functor_obj_hom_hom_apply inverse_obj_X
  inverse_obj_point inverse_map_toFun unitIso_hom_app_toFun unitIso_inv_app_toFun
  counitIso_hom_app_right_hom_apply counitIso_inv_app_right_hom_apply]
def equivUnderPUnit : Pointed.{u} ≌ Under (PUnit.{u + 1} : Type u) where
  functor :=
    { obj X := Under.mk (TypeCat.ofHom fun _ ↦ X.point)
      map f := Under.homMk (TypeCat.ofHom f.toFun) (by ext; exact f.map_point) }
  inverse :=
    { obj A := of (A.hom PUnit.unit)
      map g := ⟨g.right, ConcreteCategory.congr_hom (Under.w g) PUnit.unit⟩ }
  unitIso := NatIso.ofComponents fun X ↦ Iso.refl X
  counitIso := NatIso.ofComponents fun A ↦
    Under.isoMk (Iso.refl A.right) (by ext; rfl)

/-- The functor `Pointed ⥤ Under PUnit` acts on morphisms by their underlying functions. This is
stated by hand: the `simps` version would mention `Under.mk` in the types of its coercion. -/
@[simp]
lemma equivUnderPUnit_functor_map_right_hom_apply {X Y : Pointed.{u}} (f : X ⟶ Y) (a : X) :
    (equivUnderPUnit.functor.map f).right a = f.toFun a :=
  rfl

instance [UnivLE.{w, u}] : HasColimitsOfSize.{w, w} Pointed.{u} :=
  Adjunction.has_colimits_of_equivalence equivUnderPUnit.functor

instance [UnivLE.{w, u}] : HasLimitsOfSize.{w, w} Pointed.{u} :=
  have : HasLimitsOfSize.{w, w} (Under (PUnit.{u + 1} : Type u)) := ⟨fun _ _ ↦ inferInstance⟩
  Adjunction.has_limits_of_equivalence equivUnderPUnit.functor

end Pointed
