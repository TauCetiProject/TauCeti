/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ext.LeftDerived
public import TauCeti.CategoryTheory.Abelian.Injective.Ext

/-!
# Balancing left-derived and right-derived `Ext`

Composing `CategoryTheory.extObjIsoLinearExtFunctor` and
`CategoryTheory.rightDerivedLinearCoyonedaIsoExt` balances left- and right-derived `Ext`
(`CategoryTheory.extObjIsoRightDerivedLinearCoyoneda`), naturally in both variables.

## Main definitions

* `CategoryTheory.extObjIsoRightDerivedLinearCoyoneda`: the natural balance isomorphism
  `(_root_.Ext k C n).obj (op X) ≅ ((linearCoyoneda k C).obj (op X)).rightDerived n`.

## Main results

* `CategoryTheory.extObjIsoRightDerivedLinearCoyoneda_hom_naturality_left`: naturality of the
  balance isomorphism in the contravariant first variable.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced Mathematics
  38, Cambridge University Press, 1994, Theorem 2.7.6 (balancing `Ext`) and Section 10.7.
-/

public section

universe v u

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
  (k : Type*) [CommRing k] [Linear k C] [EnoughProjectives C] [EnoughInjectives C]

/-- **Balancing `Ext`.** In a `k`-linear abelian category with enough projectives and enough
injectives, left-derived contravariant `Hom` and right-derived covariant `Hom` are naturally
isomorphic in the second variable. -/
noncomputable def extObjIsoRightDerivedLinearCoyoneda (X : C) (n : ℕ) :
    (_root_.Ext k C n).obj (op X) ≅ ((linearCoyoneda k C).obj (op X)).rightDerived n :=
  extObjIsoLinearExtFunctor k X n ≪≫ (rightDerivedLinearCoyonedaIsoExt k X n).symm

/-- `extObjIsoRightDerivedLinearCoyoneda` is the composite of `extObjIsoLinearExtFunctor` and the
inverse of `rightDerivedLinearCoyonedaIsoExt`. -/
@[simp]
lemma extObjIsoRightDerivedLinearCoyoneda_hom (X : C) (n : ℕ) :
    (extObjIsoRightDerivedLinearCoyoneda k X n).hom =
      (extObjIsoLinearExtFunctor k X n).hom ≫ (rightDerivedLinearCoyonedaIsoExt k X n).inv := (rfl)

/-- The inverse of `extObjIsoRightDerivedLinearCoyoneda` is the composite of
`rightDerivedLinearCoyonedaIsoExt` and the inverse of `extObjIsoLinearExtFunctor`. -/
@[simp]
lemma extObjIsoRightDerivedLinearCoyoneda_inv (X : C) (n : ℕ) :
    (extObjIsoRightDerivedLinearCoyoneda k X n).inv =
      (rightDerivedLinearCoyonedaIsoExt k X n).hom ≫ (extObjIsoLinearExtFunctor k X n).inv := (rfl)

/-- The balance isomorphism `extObjIsoRightDerivedLinearCoyoneda` is natural in the first
variable. -/
@[reassoc]
lemma extObjIsoRightDerivedLinearCoyoneda_hom_naturality_left {X X' : C} (f : X' ⟶ X) (n : ℕ) :
    (_root_.Ext k C n).map f.op ≫ (extObjIsoRightDerivedLinearCoyoneda k X' n).hom =
      (extObjIsoRightDerivedLinearCoyoneda k X n).hom ≫
        ((linearCoyoneda k C).map f.op).rightDerived n := by
  rw [← cancel_mono (rightDerivedLinearCoyonedaIsoExt k X' n).hom]
  dsimp only [extObjIsoRightDerivedLinearCoyoneda, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    extObjIsoLinearExtFunctor_hom_naturality_left, Category.assoc,
    rightDerivedLinearCoyonedaIsoExt_hom_naturality_left, Category.assoc, Iso.inv_hom_id_assoc]

/-- In degree zero, `extObjIsoRightDerivedLinearCoyoneda` identifies the canonical comparison
`extZeroIso.inv : Hom(X, Y) ⟶ Ext⁰(X, Y)` with `Functor.toRightDerivedZero`. -/
@[reassoc]
lemma extZeroIso_inv_comp_extObjIsoRightDerivedLinearCoyoneda_hom_app (X Y : C) :
    (extZeroIso (k := k) X Y).inv ≫ (extObjIsoRightDerivedLinearCoyoneda k X 0).hom.app Y =
      ((linearCoyoneda k C).obj (op X)).toRightDerivedZero.app Y := by
  refine (cancel_mono ((rightDerivedLinearCoyonedaIsoExt k X 0).hom.app Y)).1 ?_
  dsimp only [extObjIsoRightDerivedLinearCoyoneda, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  erw [Category.assoc, Category.assoc, (rightDerivedLinearCoyonedaIsoExt k X 0).inv_hom_id_app Y,
    Category.comp_id, extZeroIso_inv_comp_extObjIsoLinearExtFunctor_hom_app,
    toRightDerivedZero_app_comp_rightDerivedLinearCoyonedaIsoExt_hom_app]

/-- In degree zero, the inverse of `extObjIsoRightDerivedLinearCoyoneda` sends
`Functor.toRightDerivedZero` back to `extZeroIso.inv`. -/
@[reassoc]
lemma toRightDerivedZero_app_comp_extObjIsoRightDerivedLinearCoyoneda_inv_app (X Y : C) :
    ((linearCoyoneda k C).obj (op X)).toRightDerivedZero.app Y ≫
        (extObjIsoRightDerivedLinearCoyoneda k X 0).inv.app Y =
      (extZeroIso (k := k) X Y).inv := by
  erw [← extZeroIso_inv_comp_extObjIsoRightDerivedLinearCoyoneda_hom_app, Category.assoc,
    (extObjIsoRightDerivedLinearCoyoneda k X 0).hom_inv_id_app Y, Category.comp_id]

/-- In degree zero, when `Hom(X, -)` preserves finite limits, `extObjIsoRightDerivedLinearCoyoneda`
is compatible with `Functor.rightDerivedZeroIsoSelf` and `extZeroIso`. -/
@[reassoc]
lemma extObjIsoRightDerivedLinearCoyoneda_hom_app_comp_rightDerivedZeroIsoSelf
    (X Y : C) [PreservesFiniteLimits ((linearCoyoneda k C).obj (op X))] :
    (extObjIsoRightDerivedLinearCoyoneda k X 0).hom.app Y ≫
        ((linearCoyoneda k C).obj (op X)).rightDerivedZeroIsoSelf.hom.app Y =
      (extZeroIso (k := k) X Y).hom := by
  refine (cancel_epi (extZeroIso (k := k) X Y).inv).1 ?_
  erw [extZeroIso_inv_comp_extObjIsoRightDerivedLinearCoyoneda_hom_app_assoc,
    Functor.rightDerivedZeroIsoSelf_inv_hom_id_app, Iso.inv_hom_id]
  rfl

end CategoryTheory
