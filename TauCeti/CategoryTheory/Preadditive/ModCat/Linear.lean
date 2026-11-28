/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import TauCeti.CategoryTheory.Linear.FullSubcategory
public import TauCeti.CategoryTheory.Preadditive.AdditiveFunctor

import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Module-valued lifts of additive functors

For an additive functor from an `R`-linear preadditive category to abelian groups, the
endomorphisms `F.map (r • 𝟙 X)` give each value `F.obj X` an `R`-module structure.
This action lifts the functor and its natural transformations to `ModuleCat R`.
For a commutative ring, forgetting this structure gives an equivalence from the
category of additive, `R`-linear module-valued functors to the category of additive
abelian-group-valued functors. Taking the source to be an opposite category applies
this to modules over a linear category.

## References

* B. Mitchell, *Rings with several objects*, Adv. Math. 8 (1972), §11, pp. 50–51.
  The lift uses Mitchell's action of the source's center on additive functors.
-/

public section

universe w

open CategoryTheory Limits

namespace CategoryTheory.AdditiveFunctor

variable {D : Type*} [Category* D] [Preadditive D]

section Semiring

variable (R : Type*) [Semiring R] [Linear R D]
variable (F : D ⥤+ AddCommGrpCat.{w})

/-- The module structure at an object of an additive functor induced by the scalar action
on identities in the source. -/
@[instance_reducible]
def valueModule (X : D) : Module R (F.obj.obj X) :=
  Module.compHom (F.obj.obj X) (R := AddMonoid.End (F.obj.obj X))
    { toFun r := ((smulEnd R r F).hom.app X).hom
      map_one' := by
        -- The identity of additive functors is pointwise the identity endomorphism.
        rw [smulEnd_one]; rfl
      map_zero' := by
        -- The zero morphism of additive functors is pointwise the zero endomorphism.
        rw [smulEnd_zero]; rfl
      map_add' r s :=
        congrArg (fun t : F ⟶ F ↦ (t.hom.app X).hom) (smulEnd_add R r s F)
      map_mul' r s :=
        congrArg (fun t : F ⟶ F ↦ (t.hom.app X).hom) (smulEnd_mul R r s F) }

/-- A scalar acts on an element through the image of the corresponding scalar identity. -/
@[simp]
theorem valueModule_smul (X : D) (r : R) (x : F.obj.obj X) :
    (valueModule R F X).smul r x = F.obj.map (r • 𝟙 X) x := by
  exact ConcreteCategory.congr_hom (smulEnd_hom_app R r F X) x

/-- The maps of an additive functor commute with the source-induced scalar action. -/
theorem map_valueModule_smul {X Y : D} (f : X ⟶ Y) (r : R) (x : F.obj.obj X) :
    F.obj.map f ((valueModule R F X).smul r x) =
      (valueModule R F Y).smul r (F.obj.map f x) := by
  simpa only [valueModule_smul, ConcreteCategory.comp_apply, smulEnd_hom_app] using
    (ConcreteCategory.congr_hom ((smulEnd R r F).hom.naturality f) x).symm

/-- Natural transformations commute with the source-induced scalar actions on their values. -/
theorem natTrans_valueModule_smul {F G : D ⥤+ AddCommGrpCat.{w}}
    (α : F ⟶ G) (X : D) (r : R) (x : F.obj.obj X) :
    α.hom.app X ((valueModule R F X).smul r x) =
      (valueModule R G X).smul r (α.hom.app X x) := by
  simpa only [valueModule_smul, ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom (α.hom.naturality (r • 𝟙 X)) x

end Semiring

variable (R : Type*) [Ring R] [Linear R D]
variable (F : D ⥤+ AddCommGrpCat.{w})

/-- The value of an additive functor equipped with its source-induced module structure. -/
@[expose]
def moduleObj (X : D) : ModuleCat.{w} R :=
  @ModuleCat.of R _ (F.obj.obj X) _ (valueModule R F X)

/-- The scalar action in the module obtained by evaluating an additive functor. -/
@[simp]
theorem moduleObj_smul (X : D) (r : R) (x : moduleObj R F X) :
    (r • x : moduleObj R F X) = F.obj.map (r • 𝟙 X) x :=
  valueModule_smul R F X r x

/-- Lift an additive functor to modules by giving its values the source-induced scalar action.
The value at each object has the same underlying type as the original abelian group. -/
@[expose]
def liftToModuleCat : D ⥤ ModuleCat.{w} R where
  obj := moduleObj R F
  map f := ConcreteCategory.ofHom (C := ModuleCat R)
    { (F.obj.map f).hom with map_smul' := map_valueModule_smul R F f }
  map_id X := ModuleCat.hom_ext <| LinearMap.ext fun x ↦
    ConcreteCategory.congr_hom (F.obj.map_id X) x
  map_comp f g := ModuleCat.hom_ext <| LinearMap.ext fun x ↦
    ConcreteCategory.congr_hom (F.obj.map_comp f g) x

/-- The lift acts on morphisms by the original additive map. -/
@[simp]
theorem liftToModuleCat_map_apply {X Y : D} (f : X ⟶ Y)
    (x : (liftToModuleCat R F).obj X) :
    ((liftToModuleCat R F).map f).hom x = F.obj.map f x := (rfl)

/-- The scalar action on the values of the lifted functor. -/
@[simp]
theorem liftToModuleCat_smul (X : D) (r : R) (x : (liftToModuleCat R F).obj X) :
    (r • x : (liftToModuleCat R F).obj X) = F.obj.map (r • 𝟙 X) x :=
  valueModule_smul R F X r x

instance : (liftToModuleCat R F).Additive where
  map_add := by
    intro X Y f g
    ext x
    simp only [ModuleCat.hom_add, LinearMap.add_apply, liftToModuleCat_map_apply]
    exact (ConcreteCategory.congr_hom (F.obj.map_add (f := f) (g := g)) x).trans
      (AddCommGrpCat.hom_add_apply (F.obj.map f) (F.obj.map g) x)

/-- Forgetting the scalars of the lift recovers the original abelian-group-valued functor. -/
def liftToModuleCatForgetIso :
    liftToModuleCat R F ⋙ forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w} ≅ F.obj :=
  NatIso.ofComponents (fun X ↦ Iso.refl (F.obj.obj X)) (by
    intro X Y f
    simp only [Functor.comp_map, Iso.refl_hom]
    -- Forgetting a lifted map retains its original additive map by definition.
    rfl)

-- Simplify the application before simp rewrites the objects in its type.
/-- The forgetful comparison acts as the identity on elements. -/
@[simp↓]
theorem liftToModuleCatForgetIso_hom_app_apply (X : D) (x : F.obj.obj X) :
    ((liftToModuleCatForgetIso R F).hom.app X) x = x := (rfl)

/-- The inverse forgetful comparison acts as the identity on elements. -/
@[simp↓]
theorem liftToModuleCatForgetIso_inv_app_apply (X : D) (x : F.obj.obj X) :
    ((liftToModuleCatForgetIso R F).inv.app X) x = x := (rfl)

variable (D) in
/-- The module-valued lift on additive functors and their natural transformations. -/
@[expose]
def liftToModuleCatFunctor : (D ⥤+ AddCommGrpCat.{w}) ⥤ D ⥤ ModuleCat.{w} R where
  obj := liftToModuleCat R
  map {F G} α :=
    { app X := ConcreteCategory.ofHom (C := ModuleCat R)
        { (α.hom.app X).hom with
          map_smul' := natTrans_valueModule_smul R α X }
      naturality X Y f := ModuleCat.hom_ext <| LinearMap.ext fun x ↦
        ConcreteCategory.congr_hom (α.hom.naturality f) x }
  map_id F := by ext X x; rfl
  map_comp α β := by ext X x; rfl

/-- The lift functor equips an additive functor with its source-induced scalar action. -/
@[simp]
theorem liftToModuleCatFunctor_obj :
    (liftToModuleCatFunctor D R).obj F = F.liftToModuleCat R := (rfl)

/-- The component of a lifted natural transformation is the original additive map. -/
@[simp]
theorem liftToModuleCatFunctor_map_app_apply {F G : D ⥤+ AddCommGrpCat.{w}} (α : F ⟶ G)
    (X : D) (x : (F.liftToModuleCat R).obj X) :
    (((liftToModuleCatFunctor (D := D) R).map α).app X).hom x = α.hom.app X x := (rfl)

variable (D) in
/-- Forgetting the scalars of the module-valued lift recovers the inclusion of additive
functors into the functor category. -/
def liftToModuleCatFunctorForgetIso :
    liftToModuleCatFunctor.{w} D R ⋙
      (Functor.whiskeringRight D _ _).obj (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) ≅
      (additiveFunctor D AddCommGrpCat.{w}).ι :=
  NatIso.ofComponents (fun F ↦ F.liftToModuleCatForgetIso R) (by
    intro F G α
    apply NatTrans.ext
    funext X
    simp only [Functor.comp_map, Functor.whiskeringRight_obj_map, Functor.whiskerRight_app,
      NatTrans.comp_app, ObjectProperty.ι_map]
    apply AddCommGrpCat.ext
    intro x
    simp only [ConcreteCategory.comp_apply]
    rewrite (config := { transparency := .default })
      [liftToModuleCatForgetIso_hom_app_apply R G X, ModuleCat.forget₂_map]
    exact liftToModuleCatFunctor_map_app_apply R α X x)

/-- The functorial comparison at each additive functor is its pointwise forgetful comparison. -/
@[simp]
theorem liftToModuleCatFunctorForgetIso_app (F : D ⥤+ AddCommGrpCat.{w}) :
    (liftToModuleCatFunctorForgetIso D R).app F = F.liftToModuleCatForgetIso R := (rfl)

variable (D) in
private abbrev whiskerForgetScalars : (D ⥤ ModuleCat.{w} R) ⥤ D ⥤ AddCommGrpCat.{w} :=
  (Functor.whiskeringRight D _ _).obj (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})

instance : (liftToModuleCatFunctor.{w} D R).Additive := by
  have : (liftToModuleCatFunctor.{w} D R ⋙ whiskerForgetScalars D R).Additive :=
    Functor.additive_of_iso (liftToModuleCatFunctorForgetIso D R).symm
  exact Functor.additive_of_comp_faithful _ (whiskerForgetScalars D R)

instance : (liftToModuleCatFunctor.{w} D R).Faithful :=
  Functor.Faithful.of_comp_iso (liftToModuleCatFunctorForgetIso D R)

instance : PreservesFiniteLimits (liftToModuleCatFunctor.{w} D R) := by
  have : HasLimitsOfSize.{0, 0} (ModuleCat.{w} R) := ModuleCat.hasLimitsOfSize.{0, 0, w}
  have : PreservesFiniteLimits (additiveFunctor D AddCommGrpCat.{w}).ι :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteLimits (liftToModuleCatFunctor.{w} D R ⋙ whiskerForgetScalars D R) :=
    preservesFiniteLimits_of_natIso (liftToModuleCatFunctorForgetIso D R).symm
  have : ReflectsFiniteLimits (whiskerForgetScalars.{w} D R) := ⟨fun _ _ _ ↦ inferInstance⟩
  exact preservesFiniteLimits_of_reflects_of_preserves (liftToModuleCatFunctor.{w} D R)
    (whiskerForgetScalars D R)

instance : PreservesFiniteColimits (liftToModuleCatFunctor.{w} D R) := by
  have : PreservesFiniteColimits (additiveFunctor D AddCommGrpCat.{w}).ι :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteColimits (liftToModuleCatFunctor.{w} D R ⋙ whiskerForgetScalars D R) :=
    preservesFiniteColimits_of_natIso (liftToModuleCatFunctorForgetIso D R).symm
  have : ReflectsFiniteColimits (whiskerForgetScalars.{w} D R) :=
    { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  exact preservesFiniteColimits_of_reflects_of_preserves (liftToModuleCatFunctor.{w} D R)
    (whiskerForgetScalars D R)

end CategoryTheory.AdditiveFunctor

namespace CategoryTheory.Functor

variable {R : Type*} [CommRing R]
variable {D : Type*} [Category* D] [Preadditive D] [CategoryTheory.Linear R D]
variable (G : D ⥤ ModuleCat.{w} R) [G.Additive] [G.Linear R]

/-- Lifting an additive linear functor after forgetting its scalars recovers the original
module-valued functor. -/
def liftToModuleCatForgetLinearIso :
    (AdditiveFunctor.of (G ⋙ forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})).liftToModuleCat R ≅ G :=
  let F := AdditiveFunctor.of (G ⋙ forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})
  NatIso.ofComponents (fun X ↦
    ModuleCat.isoMk ((F.liftToModuleCatForgetIso R).app X) (fun r ↦ by
      ext x
      -- The underlying comparison is the identity, so compatibility is the scalar-action formula.
      have h : G.map (r • 𝟙 X) = r • 𝟙 (G.obj X) := by simp
      exact ((AdditiveFunctor.liftToModuleCat_smul R F X r x).trans
        (ConcreteCategory.congr_hom h x)).symm)) (by
    intro X Y f
    apply ModuleCat.hom_ext
    ext x
    -- The lifted map uses the original map, and the comparison acts as the identity on elements.
    rfl)

/-- The comparison with the original linear functor acts as the identity on elements. -/
@[simp↓]
theorem liftToModuleCatForgetLinearIso_hom_app_apply (X : D) (x : G.obj X) :
    (G.liftToModuleCatForgetLinearIso.hom.app X) x = x := (rfl)

/-- The inverse comparison with the original linear functor acts as the identity on elements. -/
@[simp↓]
theorem liftToModuleCatForgetLinearIso_inv_app_apply (X : D) (x : G.obj X) :
    (G.liftToModuleCatForgetLinearIso.inv.app X) x = x := (rfl)

end CategoryTheory.Functor

namespace TauCeti

variable {R : Type*} [CommRing R]
variable {D : Type*} [Category* D] [Preadditive D] [Linear R D]

instance (F : D ⥤+ AddCommGrpCat.{w}) :
    (F.liftToModuleCat R).Linear R :=
  (Functor.linear_iff R _).2 fun X r ↦ by
    ext x
    simp only [ModuleCat.hom_smul, LinearMap.smul_apply, ModuleCat.hom_id, LinearMap.id_apply]
    exact (AdditiveFunctor.liftToModuleCat_map_apply R F (r • 𝟙 X) x).trans
      (AdditiveFunctor.liftToModuleCat_smul R F X r x).symm

variable (R D) in
/-- The object property of being an additive and `R`-linear functor to `R`-modules. -/
def linearModuleFunctor : ObjectProperty (D ⥤ ModuleCat.{w} R) :=
  fun F ↦ F.Additive ∧ F.Linear R

/-- Membership in the full subcategory of linear module-valued functors. -/
@[simp]
theorem linearModuleFunctor_iff (F : D ⥤ ModuleCat.{w} R) :
    linearModuleFunctor R D F ↔ F.Additive ∧ F.Linear R := Iff.rfl

local instance (F : (linearModuleFunctor.{w} R D).FullSubcategory) : F.obj.Additive :=
  ((linearModuleFunctor_iff F.obj).1 F.property).1

local instance (F : (linearModuleFunctor.{w} R D).FullSubcategory) : F.obj.Linear R :=
  ((linearModuleFunctor_iff F.obj).1 F.property).2

variable (R D) in
/-- Forget scalar multiplication in each value of an additive linear functor. -/
abbrev linearModuleFunctorForget :
    (linearModuleFunctor R D).FullSubcategory ⥤ (D ⥤+ AddCommGrpCat.{w}) :=
  ObjectProperty.lift _ ((linearModuleFunctor R D).ι ⋙
      (Functor.whiskeringRight D _ _).obj (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}))
    fun F ↦ (additiveFunctor_iff _).2
      (inferInstanceAs (F.obj ⋙ forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}).Additive)

variable (R D) in
/-- Equip additive abelian-group-valued functors and their morphisms with the canonical scalars. -/
abbrev linearModuleFunctorLift :
    (D ⥤+ AddCommGrpCat.{w}) ⥤ (linearModuleFunctor R D).FullSubcategory :=
  ObjectProperty.lift _ (AdditiveFunctor.liftToModuleCatFunctor (D := D) R)
    fun F ↦ (linearModuleFunctor_iff _).2 ⟨inferInstanceAs (F.liftToModuleCat R).Additive,
      inferInstanceAs ((F.liftToModuleCat R).Linear R)⟩

variable (R D) in
/-- Additive functors to abelian groups on an `R`-linear category are equivalent to additive
`R`-linear functors to `R`-modules, via the canonical module-valued lift.
The definition is exposed so both sides of each unit and counit component have definitionally
equal underlying types in downstream modules. -/
@[expose]
def linearModuleFunctorEquiv :
    (D ⥤+ AddCommGrpCat.{w}) ≌ (linearModuleFunctor R D).FullSubcategory :=
  CategoryTheory.Equivalence.mk (linearModuleFunctorLift R D) (linearModuleFunctorForget R D)
    (NatIso.ofComponents (fun F ↦
      (additiveFunctor D AddCommGrpCat).fullyFaithfulι.preimageIso
        (F.liftToModuleCatForgetIso R).symm) (by
      intro F G α
      apply ObjectProperty.hom_ext
      ext X x
      -- Taking the preimage of the forgetful comparison preserves its identity components.
      rfl))
    (NatIso.ofComponents (fun F ↦
      (linearModuleFunctor R D).fullyFaithfulι.preimageIso F.obj.liftToModuleCatForgetLinearIso) (by
      intro F G α
      apply ObjectProperty.hom_ext
      ext X x
      -- The counit components act as the identity on elements.
      rfl))

/-- The forward functor of the equivalence is the canonical scalar lift. -/
@[simp]
theorem linearModuleFunctorEquiv_functor :
    (linearModuleFunctorEquiv.{w} R D).functor = linearModuleFunctorLift R D := (rfl)

/-- The inverse functor of the equivalence forgets the scalars. -/
@[simp]
theorem linearModuleFunctorEquiv_inverse :
    (linearModuleFunctorEquiv.{w} R D).inverse = linearModuleFunctorForget R D := (rfl)

-- Simplify the applications before simp rewrites their source and target objects.
/-- The unit of the scalar lift equivalence acts as the identity on elements. -/
@[simp↓]
theorem linearModuleFunctorEquiv_unitIso_hom_app_apply (F : D ⥤+ AddCommGrpCat.{w})
    (X : D) (x : F.obj.obj X) :
    (((linearModuleFunctorEquiv R D).unitIso.hom.app F).hom.app X) x = x := (rfl)

/-- The inverse unit of the scalar lift equivalence acts as the identity on elements. -/
@[simp↓]
theorem linearModuleFunctorEquiv_unitIso_inv_app_apply (F : D ⥤+ AddCommGrpCat.{w})
    (X : D) (x : F.obj.obj X) :
    (((linearModuleFunctorEquiv R D).unitIso.inv.app F).hom.app X) x = x := (rfl)

/-- The counit of the scalar lift equivalence acts as the identity on elements. -/
@[simp↓]
theorem linearModuleFunctorEquiv_counitIso_hom_app_apply
    (F : (linearModuleFunctor.{w} R D).FullSubcategory) (X : D) (x : F.obj.obj X) :
    (((linearModuleFunctorEquiv R D).counitIso.hom.app F).hom.app X) x = x :=
  F.obj.liftToModuleCatForgetLinearIso_hom_app_apply X x

/-- The inverse counit of the scalar lift equivalence acts as the identity on elements. -/
@[simp↓]
theorem linearModuleFunctorEquiv_counitIso_inv_app_apply
    (F : (linearModuleFunctor.{w} R D).FullSubcategory) (X : D) (x : F.obj.obj X) :
    (((linearModuleFunctorEquiv R D).counitIso.inv.app F).hom.app X) x = x :=
  F.obj.liftToModuleCatForgetLinearIso_inv_app_apply X x

section SourceLinear

attribute [local instance] AdditiveFunctor.sourceLinear

/-- The module-valued lift respects the source-induced linear structure on additive functors and the
pointwise linear structure on functors to modules. -/
instance _root_.CategoryTheory.AdditiveFunctor.liftToModuleCatFunctor_linear :
    (AdditiveFunctor.liftToModuleCatFunctor.{w} D R).Linear R where
  map_smul {F G} α r := by
    ext X x
    simp only [NatTrans.app_smul, ModuleCat.hom_smul, LinearMap.smul_apply]
    rw [AdditiveFunctor.liftToModuleCatFunctor_map_app_apply R (r • α) X x,
      AdditiveFunctor.liftToModuleCatFunctor_map_app_apply R α X x]
    rw [AdditiveFunctor.sourceLinear_smul_hom_app]
    -- The target value is the lifted module of G by liftToModuleCatFunctor_obj.
    exact (AdditiveFunctor.liftToModuleCat_smul R G X r (α.hom.app X x)).symm

/-- The scalar lift into the full subcategory of linear functors preserves scalar multiplication. -/
instance linearModuleFunctorLift_linear : (linearModuleFunctorLift.{w} R D).Linear R where
  -- The full-subcategory lift and scalar action use the ambient maps on underlying morphisms.
  map_smul α r := ObjectProperty.hom_ext (linearModuleFunctor R D) <|
    (AdditiveFunctor.liftToModuleCatFunctor D R).map_smul r α

/-- The forward functor of the scalar lift equivalence is linear for the source-induced action. -/
instance linearModuleFunctorEquiv_functor_linear :
    ((linearModuleFunctorEquiv.{w} R D).functor).Linear R :=
  inferInstanceAs ((linearModuleFunctorLift R D).Linear R)

end SourceLinear

end TauCeti
