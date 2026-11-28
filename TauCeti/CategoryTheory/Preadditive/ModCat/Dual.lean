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

/-- The dual of a module with respect to a fixed scalar module `E`, with value
`Hom_R(F(X), E)` at `X` and precomposition on morphisms in both variables. -/
def dual : (ModCat.{w} C)ᵒᵖ ⥤ ModCat.{w} Cᵒᵖ :=
  (additiveFunctor Cᵒᵖᵒᵖ AddCommGrpCat.{w}).lift (dualUnderlying R E)
    fun F ↦ (additiveFunctor_iff _).2
      (inferInstanceAs ((F.unop.liftToModuleCat R).op ⋙ preadditiveYoneda.obj E).Additive)

/-- The value of the dual at `X` is the group of linear maps from the lifted value
of the original module at `X.unop` to `E`. -/
def dualValueIso (F : ModCat.{w} C) (X : Cᵒᵖᵒᵖ) :
    ((dual R E).obj (op F)).obj.obj X ≅ AddCommGrpCat.of (F.moduleObj R X.unop ⟶ E) :=
  Iso.refl _

/-- The indexing morphisms of the dual act by precomposition with the lifted maps. -/
@[simp]
theorem dual_obj_map_apply (F : ModCat.{w} C) {X Y : Cᵒᵖᵒᵖ} (f : X ⟶ Y)
    (g : ((dual R E).obj (op F)).obj.obj X) :
    (dualValueIso R E F Y).hom (((dual R E).obj (op F)).obj.map f g) =
      (F.liftToModuleCat R).map f.unop ≫ (dualValueIso R E F X).hom g := (rfl)

/-- The dual of a natural transformation acts by precomposition with its lifted components. -/
@[simp]
theorem dual_map_app_apply {F G : ModCat.{w} C} (α : F ⟶ G) (X : Cᵒᵖᵒᵖ)
    (g : ((dual R E).obj (op G)).obj.obj X) :
    (dualValueIso R E F X).hom (((dual R E).map α.op).hom.app X g) =
      ((AdditiveFunctor.liftToModuleCatFunctor Cᵒᵖ R).map α).app X.unop ≫
        (dualValueIso R E G X).hom g := (rfl)

instance : (dual (C := C) R E).Additive where
  map_add {F G} α β := by
    apply ObjectProperty.hom_ext
    ext X g
    -- Opposites reverse precomposition, and both additions are pointwise on components.
    change ((AdditiveFunctor.liftToModuleCatFunctor Cᵒᵖ R).map (α + β).unop).app X.unop ≫ g =
      ((AdditiveFunctor.liftToModuleCatFunctor Cᵒᵖ R).map α.unop).app X.unop ≫ g +
      ((AdditiveFunctor.liftToModuleCatFunctor Cᵒᵖ R).map β.unop).app X.unop ≫ g
    simp only [unop_add, Functor.map_add, NatTrans.app_add]
    exact Preadditive.add_comp _ _ _ _ _ _

/-- Forgetting the additivity witness of the dual recovers the scalar lift followed by
pointwise preadditive Yoneda. -/
private def dualCompInclusionIso :
    dual (C := C) R E ⋙ (additiveFunctor Cᵒᵖᵒᵖ AddCommGrpCat.{w}).ι ≅ dualUnderlying R E :=
  ObjectProperty.liftCompιIso _ _ _

/-- The contravariant dual sends finite colimits of modules to limits. -/
instance : PreservesFiniteLimits (dual (C := C) R E) := by
  constructor
  intro J _ _
  have := preservesFiniteLimits_op (AdditiveFunctor.liftToModuleCatFunctor.{w} Cᵒᵖ R)
  have : HasLimitsOfShape J (ModuleCat.{w} R)ᵒᵖ := inferInstance
  have : PreservesLimitsOfShape J (dualUnderlying (C := C) R E) := inferInstance
  have := preservesLimitsOfShape_of_natIso (J := J) (dualCompInclusionIso (C := C) R E).symm
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (additiveFunctor Cᵒᵖᵒᵖ AddCommGrpCat.{w}).ι

/-- For injective `E`, the dual takes finite colimits in the opposite module category to finite
colimits. Together with finite limit preservation, this makes the contravariant dual exact. -/
instance [Injective E] : PreservesFiniteColimits (dual (C := C) R E) := by
  constructor
  intro J _ _
  have := preservesFiniteColimits_op (AdditiveFunctor.liftToModuleCatFunctor.{w} Cᵒᵖ R)
  have : PreservesFiniteColimits (preadditiveYoneda.obj E) := by
    rw [preadditiveYoneda_obj]
    infer_instance
  have : HasColimitsOfSize.{0, 0} (ModuleCat.{w} R)ᵒᵖ := inferInstance
  have : PreservesColimitsOfShape J (dualUnderlying (C := C) R E) := inferInstance
  have := preservesColimitsOfShape_of_natIso (J := J) (dualCompInclusionIso (C := C) R E).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves _
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
