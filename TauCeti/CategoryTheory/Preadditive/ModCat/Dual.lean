/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Basic
public import Mathlib.CategoryTheory.Generator.Basic
public import TauCeti.CategoryTheory.Preadditive.ModCat.Basic
public import TauCeti.CategoryTheory.Preadditive.ModCat.Linear

import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Generator.Preadditive
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import TauCeti.CategoryTheory.Limits.Shapes.ZeroMorphisms
import TauCeti.CategoryTheory.Preadditive.Yoneda

/-!
# Duals of modules over a linear category

For an additive module `F` over an `R`-linear category, `ModCat.dual R E` takes the
`R`-linear Hom into a fixed scalar module `E` at each value of `F`. It reverses
morphisms in the indexing category as well as natural transformations in `F`.
The resulting functor is exact for injective `E` and faithful for a cogenerator
`E`. The construction uses the module-valued lift and Mathlib's preadditive Yoneda
functor.

Stenström, *Purity in functor categories*, J. Algebra 8 (1968), 352–361, Theorem 1,
uses the corresponding pointwise dual over the integers in the tensor–Hom comparison.
-/

public section

open CategoryTheory Limits Opposite

universe w v u r

namespace TauCeti.ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (R : Type r) [Ring R] [Linear R C] (E : ModuleCat.{w} R)

private abbrev dualUnderlying :
    (ModCat.{w} C)ᵒᵖ ⥤ Cᵒᵖᵒᵖ ⥤ AddCommGrpCat.{w} :=
  (AdditiveFunctor.liftToModuleCatFunctor Cᵒᵖ R).op ⋙
    (Functor.opUnopEquiv Cᵒᵖ (ModuleCat.{w} R)).functor ⋙
      (Functor.whiskeringRight _ _ _).obj (preadditiveYoneda.obj E)

private theorem dualUnderlying_obj (F : (ModCat.{w} C)ᵒᵖ) :
    (dualUnderlying R E).obj F = (F.unop.liftToModuleCat R).op ⋙ preadditiveYoneda.obj E := by
  simp only [Functor.comp_obj, Functor.op_obj, Functor.opUnopEquiv_functor, Functor.opHom_obj,
    AdditiveFunctor.liftToModuleCatFunctor_obj, Functor.whiskeringRight_obj_obj]

private theorem dualUnderlying_map_app_apply {F G : ModCat.{w} C} (α : F ⟶ G) (X : Cᵒᵖᵒᵖ)
    (g : G.moduleObj R X.unop ⟶ E) :
    ((dualUnderlying R E).map α.op).app X g =
      ((AdditiveFunctor.liftToModuleCatFunctor Cᵒᵖ R).map α).app X.unop ≫ g := by
  simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op,
    Functor.whiskeringRight_obj_map, Functor.whiskerRight_app]
  exact preadditiveYoneda_obj_map_apply
    (((AdditiveFunctor.liftToModuleCatFunctor Cᵒᵖ R).map α).app X.unop).op g

/-- The dual of a module with respect to a fixed scalar module `E`, with value
`Hom_R(F(X), E)` at `X` and precomposition on morphisms in both variables. -/
def dual : (ModCat.{w} C)ᵒᵖ ⥤ ModCat.{w} Cᵒᵖ :=
  (additiveFunctor Cᵒᵖᵒᵖ AddCommGrpCat.{w}).lift (dualUnderlying R E)
    fun F ↦ (additiveFunctor_iff _).2 (by rw [dualUnderlying_obj]; infer_instance)

/-- Forgetting the additivity witness of the dual recovers the scalar lift followed by
pointwise preadditive Yoneda. -/
private def dualCompInclusionIso :
    dual (C := C) R E ⋙ (additiveFunctor Cᵒᵖᵒᵖ AddCommGrpCat.{w}).ι ≅ dualUnderlying R E :=
  ObjectProperty.liftCompιIso _ _ _

private def dualObjIso (F : ModCat.{w} C) :
    ((dual R E).obj (op F)).obj ≅ (F.liftToModuleCat R).op ⋙ preadditiveYoneda.obj E :=
  (dualCompInclusionIso R E).app (op F) ≪≫ eqToIso (dualUnderlying_obj R E (op F))

/-- The value of the dual at `X` is the group of linear maps from the lifted value
of the original module at `X.unop` to `E`. -/
def dualValueIso (F : ModCat.{w} C) (X : Cᵒᵖᵒᵖ) :
    ((dual R E).obj (op F)).obj.obj X ≅ AddCommGrpCat.of (F.moduleObj R X.unop ⟶ E) :=
  (dualObjIso R E F).app X

/-- The indexing morphisms of the dual act by precomposition with the lifted maps. -/
@[simp↓]
theorem dual_obj_map_apply (F : ModCat.{w} C) {X Y : Cᵒᵖᵒᵖ} (f : X ⟶ Y)
    (g : ((dual R E).obj (op F)).obj.obj X) :
    (dualValueIso R E F Y).hom (((dual R E).obj (op F)).obj.map f g) =
      (F.liftToModuleCat R).map f.unop ≫ (dualValueIso R E F X).hom g := by
  refine Eq.trans ?_ (preadditiveYoneda_obj_map_apply ((F.liftToModuleCat R).map f.unop).op
    ((dualValueIso R E F X).hom g))
  simpa only [dualValueIso, ConcreteCategory.comp_apply, Functor.comp_map, Functor.op_map] using!
    ConcreteCategory.congr_hom ((dualObjIso R E F).hom.naturality f) g

/-- The dual of a natural transformation acts by precomposition with its lifted components. -/
@[simp↓]
theorem dual_map_app_apply {F G : ModCat.{w} C} (α : F ⟶ G) (X : Cᵒᵖᵒᵖ)
    (g : ((dual R E).obj (op G)).obj.obj X) :
    (dualValueIso R E F X).hom (((dual R E).map α.op).hom.app X g) =
      ((AdditiveFunctor.liftToModuleCatFunctor Cᵒᵖ R).map α).app X.unop ≫
        (dualValueIso R E G X).hom g := by
  refine Eq.trans ?_ (dualUnderlying_map_app_apply R E α X ((dualValueIso R E G X).hom g))
  simpa only [dualValueIso, dualObjIso, Functor.comp_map, ObjectProperty.ι_map, NatTrans.comp_app,
    ConcreteCategory.comp_apply] using! ConcreteCategory.congr_hom
      (NatTrans.congr_app ((dualCompInclusionIso R E).hom.naturality α.op) X) g

instance : (dual (C := C) R E).Additive := by
  have h : (Functor.opHom Cᵒᵖ (ModuleCat.{w} R)).Additive :=
    ⟨fun {F G} α β ↦ by
      ext1
      funext X
      simp only [Functor.opHom_map_app, NatTrans.app_add, unop_add, op_add]⟩
  have : (Functor.opUnopEquiv Cᵒᵖ (ModuleCat.{w} R)).functor.Additive := h
  have : (dualUnderlying (C := C) R E).Additive := inferInstance
  have := Functor.additive_of_iso (dualCompInclusionIso (C := C) R E).symm
  exact Functor.additive_of_comp_faithful _ (additiveFunctor Cᵒᵖᵒᵖ AddCommGrpCat.{w}).ι

/-- The contravariant dual sends finite colimits of modules to limits. -/
instance : PreservesFiniteLimits (dual (C := C) R E) := by
  have := preservesFiniteLimits_op (AdditiveFunctor.liftToModuleCatFunctor.{w} Cᵒᵖ R)
  have : HasLimitsOfSize.{0, 0} (ModuleCat.{w} R)ᵒᵖ := inferInstance
  have : PreservesFiniteLimits (dualUnderlying (C := C) R E) := ⟨fun _ _ _ ↦ inferInstance⟩
  have := preservesFiniteLimits_of_natIso (dualCompInclusionIso (C := C) R E).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (additiveFunctor Cᵒᵖᵒᵖ AddCommGrpCat.{w}).ι

/-- For injective `E`, the dual takes finite colimits in the opposite module category to finite
colimits. Together with finite limit preservation, this makes the contravariant dual exact. -/
instance [Injective E] : PreservesFiniteColimits (dual (C := C) R E) := by
  have := preservesFiniteColimits_op (AdditiveFunctor.liftToModuleCatFunctor.{w} Cᵒᵖ R)
  have : PreservesFiniteColimits (preadditiveYoneda.obj E) := by
    rw [preadditiveYoneda_obj]
    infer_instance
  have : HasColimitsOfSize.{0, 0} (ModuleCat.{w} R)ᵒᵖ := inferInstance
  have : PreservesFiniteColimits (dualUnderlying (C := C) R E) := ⟨fun _ _ _ ↦ inferInstance⟩
  have := preservesFiniteColimits_of_natIso (dualCompInclusionIso (C := C) R E).symm
  exact preservesFiniteColimits_of_reflects_of_preserves _
    (additiveFunctor Cᵒᵖᵒᵖ AddCommGrpCat.{w}).ι

/-- A cogenerator of scalar modules makes the dual faithful. -/
theorem dual_faithful (hE : IsCoseparator E) : (dual (C := C) R E).Faithful := by
  have := (isCoseparator_iff_faithful_preadditiveYoneda E).mp hE
  have : (dualUnderlying (C := C) R E).Faithful := inferInstance
  exact Functor.Faithful.of_comp_iso (dualCompInclusionIso R E)

/-- Dualizing into a cogenerator gives a zero module exactly for zero modules. -/
theorem isZero_dual_obj_iff (hE : IsCoseparator E) (F : ModCat.{w} C) :
    IsZero ((dual R E).obj (op F)) ↔ IsZero F := by
  have := dual_faithful (C := C) R E hE
  exact ⟨fun h ↦ ((dual R E).isZero_of_isZero_obj h).unop, fun h ↦ (dual R E).map_isZero h.op⟩

end TauCeti.ModCat
