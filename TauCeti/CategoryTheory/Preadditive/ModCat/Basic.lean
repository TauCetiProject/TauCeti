/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Subcategory
public import TauCeti.CategoryTheory.FinitelyPresentedFunctor.Basic

/-!
# Modules over a preadditive category

Let `C` be a preadditive category. A `C`-module is a contravariant additive functor
`Cᵒᵖ ⥤ AddCommGrpCat`, and `TauCeti.ModCat C := Cᵒᵖ ⥤+ AddCommGrpCat.{w}` is the category of
`C`-modules, the full subcategory of additive functors in `Cᵒᵖ ⥤ AddCommGrpCat.{w}`. Covariant
additive functors `C ⥤ AddCommGrpCat` are the objects of `ModCat Cᵒᵖ`. For a ring `A`, the category
`ModCat (SingleObj Aᵐᵒᵖ)` is the category of left `A`-modules.

The additive functors contain zero and are closed under kernels, cokernels, and the limits and
colimits of the target (`TauCeti/CategoryTheory/Preadditive/AdditiveFunctor.lean`). Mathlib's
`CategoryTheory/Abelian/Subcategory.lean` then makes `ModCat C` abelian, and it has every shape of
colimit that `AddCommGrpCat.{w}` has.

The representable functors `Hom(-, X)` form the Yoneda embedding `ModCat.yoneda : C ⥤ ModCat C`,
and they are projective by the Yoneda lemma. When `D` is linear over a ring `R`, so is the
category `D ⥤+ A` of additive functors into any preadditive `A`
(`CategoryTheory.AdditiveFunctor.sourceLinear`); in particular `ModCat D` is `R`-linear
([Mitchell, §11]). This structure is a scoped instance, not a global instance, since at `R = ℤ` it
agrees with the canonical action of the abelian groups `F ⟶ G` only propositionally. Finally,
finitely presented functors are additive, so `mod C` is a full subcategory of `ModCat C`.

## Main definitions

* `TauCeti.ModCat C`: the category `Cᵒᵖ ⥤+ AddCommGrpCat.{w}` of `C`-modules.
* `TauCeti.ModCat.yoneda C : C ⥤ ModCat C`: the Yoneda embedding `X ↦ Hom(-, X)`.
* `TauCeti.ModCat.coyonedaYonedaIsoEvaluation`: maps out of `Hom(-, X)` are computed by
  evaluation at `X`.
* `TauCeti.ModCat.ofFinitelyPresented C`: the fully faithful inclusion `mod C ⥤ ModCat C`.

## Main results

* `Abelian (ModCat C)` and `HasColimitsOfShape J (ModCat C)`, found by instance inference from
  the closure instances for additive functors and Mathlib's full-subcategory instances.
* `Projective ((ModCat.yoneda C).obj X)`: representable modules are projective.
* `TauCeti.ModCat.linear`: the scoped instance `Linear R (D ⥤+ AddCommGrpCat)` for an `R`-linear
  preadditive category `D`; after `open scoped TauCeti.ModCat`, specializing `D` to an opposite
  category gives `Linear R (ModCat D)`.

## References

* B. Mitchell, *Rings with several objects*, Adv. Math. 8 (1972), 1–161, §§3, 11.
-/

public section

universe w v u

open CategoryTheory Limits Opposite

namespace TauCeti

variable (C : Type u) [Category.{v} C] [Preadditive C]

/-- The category `Mod C` of `C`-modules: the contravariant additive functors
`Cᵒᵖ ⥤+ AddCommGrpCat.{w}`. Covariant additive functors on `C` are the objects of `ModCat Cᵒᵖ`. -/
abbrev ModCat := Cᵒᵖ ⥤+ AddCommGrpCat.{w}

/-- `Mod C` is abelian: instance inference finds this from the closure instances for
additive functors. -/
noncomputable example : Abelian (ModCat.{w} C) := inferInstance

/-- `Mod C` has every shape of colimit that `AddCommGrpCat.{w}` has, again by inference. -/
example {J : Type*} [Category J] [HasColimitsOfShape J AddCommGrpCat.{w}] :
    HasColimitsOfShape J (ModCat.{w} C) :=
  inferInstance

namespace ModCat

/-- The Yoneda embedding `X ↦ Hom(-, X)` of `C` into `Mod C`: the lift of `preadditiveYoneda`
through the full subcategory of additive functors. It is fully faithful by the `ObjectProperty.lift`
instances, and `ObjectProperty.liftCompιIso` recovers `preadditiveYoneda`. -/
abbrev yoneda : C ⥤ ModCat.{v} C :=
  ObjectProperty.lift _ preadditiveYoneda fun _ ↦ (additiveFunctor_iff _).2 inferInstance

variable {C} in
/-- Maps from a representable module are the elements at its representing object,
naturally in the target module. -/
def coyonedaYonedaIsoEvaluation (X : C) :
    coyoneda.obj (op ((yoneda C).obj X)) ≅
      (additiveFunctor Cᵒᵖ AddCommGrpCat.{v}).ι ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{v}).obj (op X) ⋙
        forget AddCommGrpCat.{v} ⋙ uliftFunctor.{u} :=
  NatIso.ofComponents (fun F ↦
    letI : F.obj.Additive := (additiveFunctor_iff _).1 F.property
    ({ toFun := fun f ↦ ULift.up (f.hom.app (op X) (𝟙 X))
       invFun := fun x ↦ ObjectProperty.homMk (preadditiveYonedaHomOfElement x.down)
       left_inv := fun f ↦ ObjectProperty.hom_ext _
         (preadditiveYoneda_obj_hom_ext (by simp))
       right_inv := fun x ↦ ULift.ext (by simp) } :
        ((yoneda C).obj X ⟶ F) ≃ ULift.{u} (F.obj.obj (op X))).toIso) (fun _ ↦ rfl)

variable {C} in
/-- The evaluation isomorphism sends a morphism to its value on the identity of `X`. -/
@[simp↓]
lemma coyonedaYonedaIsoEvaluation_hom_app_down (X : C) (F : ModCat.{v} C)
    (f : (yoneda C).obj X ⟶ F) :
    ((coyonedaYonedaIsoEvaluation X).hom.app F f).down = f.hom.app (op X) (𝟙 X) :=
  (rfl)

variable {C} in
/-- The inverse evaluation isomorphism sends an arrow to its action on the given element. -/
@[simp↓]
lemma coyonedaYonedaIsoEvaluation_inv_app_hom_app (X : C) (F : ModCat.{v} C)
    (x : ULift.{u} (F.obj.obj (op X))) (Y : Cᵒᵖ) (a : Y.unop ⟶ X) :
    ((coyonedaYonedaIsoEvaluation X).inv.app F x).hom.app Y a = F.obj.map a.op x.down := by
  let : F.obj.Additive := (additiveFunctor_iff _).1 F.property
  exact preadditiveYonedaHomOfElement_app_apply x.down Y a

/-- **Representable modules are projective.** A morphism `Hom(-, X) ⟶ G` is an element of
`G(X)` by Yoneda, and it lifts along an epimorphism `F ⟶ G`, which is surjective at `X`. -/
instance (X : C) : Projective ((yoneda C).obj X) where
  factors {E F} g π _ := by
    have := (additiveFunctor Cᵒᵖ AddCommGrpCat.{v}).preservesEpimorphisms_ι_of_isNormalMonoCategory
    have : Epi π.hom := (additiveFunctor Cᵒᵖ AddCommGrpCat.{v}).ι.map_epi π
    obtain ⟨s, hs⟩ := exists_comp_eq_preadditiveYoneda_obj_of_epi π.hom g.hom
    exact ⟨ObjectProperty.homMk s, ObjectProperty.hom_ext _ hs⟩

end ModCat

section Linear

variable {D : Type*} [Category* D] [Preadditive D]

namespace ModCat

/-- **Additive functors into abelian groups out of an `R`-linear category are `R`-linear**, with
the structure `AdditiveFunctor.sourceLinear R`. This is a scoped instance; use
`open scoped TauCeti.ModCat` to get it. It is scoped because at `R = ℤ` it competes with
Mathlib's `preadditiveIntLinear`: the two actions agree only propositionally
(`AdditiveFunctor.sourceLinear_smul_int`), not definitionally. Its low priority makes
`preadditiveIntLinear` win at `ℤ` when the scope is open. -/
scoped instance (priority := low) linear (R : Type*) [Ring R] [Linear R D] :
    Linear R (D ⥤+ AddCommGrpCat.{w}) :=
  AdditiveFunctor.sourceLinear R

end ModCat

open scoped TauCeti.ModCat in
/-- **`Mod D` is `R`-linear** when `D` is, once the scope `TauCeti.ModCat` is open: specialize
the scoped instance `ModCat.linear` to the source `Dᵒᵖ`. -/
example (R : Type*) [Ring R] [Linear R D] : Linear R (ModCat.{w} D) := inferInstance

end Linear

namespace ModCat

/-- The inclusion `mod C ⥤ Mod C` of finitely presented functors into all modules. It is fully
faithful by `ObjectProperty.fullyFaithfulιOfLE`, and `ObjectProperty.liftCompιOfLEIso` identifies
`modYoneda ⋙ ofFinitelyPresented C` with `ModCat.yoneda C`. -/
abbrev ofFinitelyPresented : (isFinitelyPresentedFunctor C).FullSubcategory ⥤ ModCat.{v} C :=
  ObjectProperty.ιOfLE (isFinitelyPresentedFunctor_le_additiveFunctor C)

end ModCat

end TauCeti
