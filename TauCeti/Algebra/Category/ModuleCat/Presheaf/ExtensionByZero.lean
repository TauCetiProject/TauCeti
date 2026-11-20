/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Exact extension by zero for presheaves of modules

For a presheaf of rings on a preorder, the left adjoint to restriction to a lower
interval preserves finite limits. It is extension by zero outside that interval.
After sheafification this gives exact extension by zero for sheaves of modules,
which makes restriction preserve injectives.

The construction adapts the lower-interval extension in
`TauCeti.CategoryTheory.PresheafExtensionByZero` to the varying scalar rings.
-/

public section

open CategoryTheory Limits Opposite ZeroObject

namespace PresheafOfModules

universe u v w

noncomputable section

variable {P : Type u} [Preorder P] (R : Pᵒᵖ ⥤ RingCat.{w}) (U : P)

namespace ExtensionByZero

/-- Restriction map of `F` along a morphism in `Pᵒᵖ` below `U`, viewed over `(R.map f).hom`. -/
private def overMap (F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)) {V W : Pᵒᵖ}
    (f : V ⟶ W) (hV : V.unop ≤ U) :
    F.obj (op (Over.mk (homOfLE hV))) ⟶
      (ModuleCat.restrictScalars (R.map f).hom).obj
        (F.obj (op (Over.mk (homOfLE ((leOfHom f.unop).trans hV))))) :=
  F.map (Over.homMk (U := Over.mk (homOfLE ((leOfHom f.unop).trans hV)))
    (V := Over.mk (homOfLE hV)) f.unop).op

@[simp]
private lemma overMap_id (F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)) {V : Pᵒᵖ}
    (hV : V.unop ≤ U) :
    overMap R U F (𝟙 V) hV =
      (ModuleCat.restrictScalarsId'App (R.map (𝟙 V)).hom
        (congrArg RingCat.Hom.hom (R.map_id V)) _).inv := by
  have hi : (Over.homMk (U := Over.mk (homOfLE hV))
      (V := Over.mk (homOfLE hV)) (𝟙 V).unop).op = 𝟙 _ :=
    Quiver.Hom.unop_inj (Over.OverMorphism.ext rfl)
  ext x
  simpa [overMap] using F.congr_map_apply hi x

@[simp]
private lemma overMap_comp (F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R))
    {V W Z : Pᵒᵖ} (f : V ⟶ W) (g : W ⟶ Z) (hV : V.unop ≤ U) :
    overMap R U F (f ≫ g) hV =
      overMap R U F f hV ≫
        (ModuleCat.restrictScalars (R.map f).hom).map
          (overMap R U F g ((leOfHom f.unop).trans hV)) ≫
        (ModuleCat.restrictScalarsComp'App (R.map f).hom (R.map g).hom (R.map (f ≫ g)).hom
          (congrArg RingCat.Hom.hom (R.map_comp f g)) _).inv := by
  have hc : (Over.homMk (U := Over.mk (homOfLE ((leOfHom (f ≫ g).unop).trans hV)))
      (V := Over.mk (homOfLE hV)) (f ≫ g).unop).op =
      (Over.homMk (U := Over.mk (homOfLE ((leOfHom f.unop).trans hV)))
        (V := Over.mk (homOfLE hV)) f.unop).op ≫
      (Over.homMk (U := Over.mk (homOfLE ((leOfHom g.unop).trans ((leOfHom f.unop).trans hV))))
        (V := Over.mk (homOfLE ((leOfHom f.unop).trans hV))) g.unop).op :=
    Quiver.Hom.unop_inj (Over.OverMorphism.ext rfl)
  ext x
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.restrictScalars.map_apply]
  exact (F.congr_map_apply hc x).trans (F.map_comp_apply _ _ x)

@[reassoc]
private lemma overMap_naturality {F G : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)}
    (α : F ⟶ G) {V W : Pᵒᵖ} (f : V ⟶ W) (hV : V.unop ≤ U) :
    overMap R U F f hV ≫
        (ModuleCat.restrictScalars (R.map f).hom).map
          (α.app (op (Over.mk (homOfLE ((leOfHom f.unop).trans hV))))) =
      α.app (op (Over.mk (homOfLE hV))) ≫ overMap R U G f hV := by
  ext x
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.restrictScalars.map_apply]
  exact PresheafOfModules.naturality_apply α _ x

open Classical in
/-- The extension of a presheaf to an object of the ambient preorder. -/
private def obj (F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)) (V : Pᵒᵖ) :
    ModuleCat.{v} (R.obj V) :=
  if h : V.unop ≤ U then F.obj (op (Over.mk (homOfLE h))) else 0

/-- On an object below `U`, extension by zero recovers the original presheaf. -/
private def objIso (F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)) {V : Pᵒᵖ}
    (h : V.unop ≤ U) : obj R U F V ≅ F.obj (op (Over.mk (homOfLE h))) :=
  eqToIso (dite_eq_left h)

private lemma isZero_obj (F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)) {V : Pᵒᵖ}
    (h : ¬ V.unop ≤ U) : IsZero (obj R U F V) := by
  rw [obj, dite_eq_right h]
  exact isZero_zero _

open Classical in
private def map (F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)) {V W : Pᵒᵖ} (f : V ⟶ W) :
    obj R U F V ⟶ (ModuleCat.restrictScalars (R.map f).hom).obj (obj R U F W) :=
  if hV : V.unop ≤ U then
    (objIso R U F hV).hom ≫ overMap R U F f hV ≫
      (ModuleCat.restrictScalars (R.map f).hom).map
        (objIso R U F ((leOfHom f.unop).trans hV)).inv
  else 0

private lemma map_hom_apply (F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)) {V W : Pᵒᵖ}
    (f : V ⟶ W) (hV : V.unop ≤ U) (x : obj R U F V) :
    (map R U F f).hom x =
      (objIso R U F ((leOfHom f.unop).trans hV)).inv.hom
        ((overMap R U F f hV).hom ((objIso R U F hV).hom.hom x)) := by
  rw [map, dite_eq_left hV]
  rfl

/-- Extension by zero of a presheaf on the lower interval of `U`. -/
private def presheaf (F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)) :
    PresheafOfModules.{v} R where
  obj := obj R U F
  map := map R U F
  map_id V := by
    by_cases h : V.unop ≤ U
    · simp only [map, dite_eq_left h, overMap_id, ModuleCat.restrictScalarsId'_inv_app]
      rw [← ModuleCat.restrictScalarsId'App_inv_naturality, Iso.hom_inv_id_assoc]
    · exact (isZero_obj R U F h).eq_of_src _ _
  map_comp {V W Z} f g := by
    by_cases h : V.unop ≤ U
    · have hW := (leOfHom f.unop).trans h
      simp only [map, dite_eq_left h, dite_eq_left hW, overMap_comp, Functor.map_comp,
        Category.assoc, Iso.inv_hom_id_map_assoc, ModuleCat.restrictScalarsComp'_inv_app]
      rw [← ModuleCat.restrictScalarsComp'App_inv_naturality]
    · simp [map, h]

@[simp]
private lemma presheaf_obj (F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)) (V : Pᵒᵖ) :
    (presheaf R U F).obj V = obj R U F V :=
  rfl

@[simp]
private lemma presheaf_map (F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)) {V W : Pᵒᵖ}
    (f : V ⟶ W) : (presheaf R U F).map f = map R U F f :=
  rfl

open Classical in
private def mapApp {F G : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)} (α : F ⟶ G) (V : Pᵒᵖ) :
    obj R U F V ⟶ obj R U G V :=
  if h : V.unop ≤ U then
    (objIso R U F h).hom ≫ α.app (op (Over.mk (homOfLE h))) ≫ (objIso R U G h).inv
  else 0

/-- Extension by zero as a functor between categories of presheaves. -/
private def functor : PresheafOfModules.{v} ((Over.forget U).op ⋙ R) ⥤ PresheafOfModules.{v} R where
  obj := presheaf R U
  map α :=
    { app := mapApp R U α
      naturality {V W} f := by
        by_cases hV : V.unop ≤ U
        · simp only [presheaf_obj, presheaf_map, map, mapApp, dite_eq_left hV,
            dite_eq_left ((leOfHom f.unop).trans hV), Functor.map_comp, Category.assoc,
            Iso.inv_hom_id_map_assoc, Iso.inv_hom_id_assoc]
          rw [reassoc_of% overMap_naturality]
        · simp [map, mapApp, hV] }
  map_id F := by
    refine PresheafOfModules.hom_ext fun V ↦ ?_
    by_cases h : V.unop ≤ U
    · simp [mapApp, h]
    · exact (isZero_obj R U F h).eq_of_src _ _
  map_comp α β := by
    refine PresheafOfModules.hom_ext fun V ↦ ?_
    by_cases h : V.unop ≤ U <;> simp [mapApp, h]

@[simp]
private lemma functor_obj_obj (F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)) (V : Pᵒᵖ) :
    ((functor R U).obj F).obj V = obj R U F V :=
  rfl

@[simp]
private lemma functor_map_app {F G : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)}
    (α : F ⟶ G) (V : Pᵒᵖ) : ((functor R U).map α).app V = mapApp R U α V :=
  rfl

/-- Evaluating the extension below `U` is naturally isomorphic to evaluating the original
presheaf. -/
private def evaluationIso {V : P} (h : V ≤ U) :
    functor R U ⋙ PresheafOfModules.evaluation R (op V) ≅
      PresheafOfModules.evaluation ((Over.forget U).op ⋙ R) (op (Over.mk (homOfLE h))) :=
  NatIso.ofComponents (fun F ↦ objIso R U F h) fun {_ G} _ ↦
    (Iso.eq_comp_inv (objIso R U G h)).mp ((dite_eq_left h).trans (Category.assoc _ _ _).symm)

private def restrictObjIso (F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)) (V : (Over U)ᵒᵖ) :
    obj R U F (op V.unop.left) ≅ F.obj V :=
  objIso R U F (leOfHom V.unop.hom)

private def restrictHom {F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)}
    {G : PresheafOfModules.{v} R} (α : presheaf R U F ⟶ G) :
    F ⟶ (PresheafOfModules.pushforward (F := Over.forget U)
      (𝟙 ((Over.forget U).op ⋙ R))).obj G where
  app V := (restrictObjIso R U F V).inv ≫ α.app (op V.unop.left)
  naturality {V W} f := by
    ext x
    have h1 := PresheafOfModules.naturality_apply α ((Over.forget U).op.map f)
      ((restrictObjIso R U F V).inv.hom x)
    have hv : (objIso R U F (V := op V.unop.left) (leOfHom V.unop.hom)).hom.hom
        ((restrictObjIso R U F V).inv.hom x) = x :=
      ModuleCat.hom_inv_apply (restrictObjIso R U F V) x
    have h2 : (map R U F ((Over.forget U).op.map f)).hom
        ((restrictObjIso R U F V).inv.hom x) =
        (restrictObjIso R U F W).inv.hom ((F.map f).hom x) := by
      rw [map_hom_apply R U F _ (leOfHom V.unop.hom)]
      exact congrArg (restrictObjIso R U F W).inv.hom
        ((congrArg (overMap R U F _ _).hom hv).trans
          (F.congr_map_apply (Quiver.Hom.unop_inj (Over.OverMorphism.ext rfl)) x))
    exact (congrArg (α.app (op W.unop.left)).hom h2).symm.trans h1

open Classical in
private def extendApp {F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)}
    {G : PresheafOfModules.{v} R}
    (α : F ⟶ (PresheafOfModules.pushforward (F := Over.forget U)
      (𝟙 ((Over.forget U).op ⋙ R))).obj G)
    (V : Pᵒᵖ) : obj R U F V ⟶ G.obj V :=
  if h : V.unop ≤ U then (objIso R U F h).hom ≫ α.app (op (Over.mk (homOfLE h))) else 0

private lemma extendApp_hom_apply {F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)}
    {G : PresheafOfModules.{v} R}
    (α : F ⟶ (PresheafOfModules.pushforward (F := Over.forget U)
      (𝟙 ((Over.forget U).op ⋙ R))).obj G)
    {V : Pᵒᵖ} (h : V.unop ≤ U) (x : obj R U F V) :
    (extendApp R U α V).hom x =
      (α.app (op (Over.mk (homOfLE h)))).hom ((objIso R U F h).hom.hom x) := by
  rw [extendApp, dite_eq_left h]
  rfl

private def extendHom {F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)}
    {G : PresheafOfModules.{v} R}
    (α : F ⟶ (PresheafOfModules.pushforward (F := Over.forget U)
      (𝟙 ((Over.forget U).op ⋙ R))).obj G) :
    presheaf R U F ⟶ G where
  app := extendApp R U α
  naturality {V W} f := by
    by_cases hV : V.unop ≤ U
    · refine ModuleCat.hom_ext (LinearMap.ext fun (x : obj R U F V) ↦ ?_)
      have hW := (leOfHom f.unop).trans hV
      have hinv := ModuleCat.hom_inv_apply (objIso R U F hW)
        ((overMap R U F f hV).hom ((objIso R U F hV).hom.hom x))
      exact (congrArg (extendApp R U α W).hom (map_hom_apply R U F f hV x)).trans
        ((extendApp_hom_apply R U α hW _).trans
          ((congrArg (α.app _).hom hinv).trans
            ((PresheafOfModules.naturality_apply α _ _).trans
              (congrArg (G.map f).hom (extendApp_hom_apply R U α hV x).symm))))
    · simp [map, extendApp, hV]

/-- Hom-set equivalence between extension by zero and restriction to the lower interval. -/
private def homEquiv (F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R))
    (G : PresheafOfModules.{v} R) :
    ((functor R U).obj F ⟶ G) ≃
      (F ⟶ (PresheafOfModules.pushforward (F := Over.forget U)
        (𝟙 ((Over.forget U).op ⋙ R))).obj G) where
  toFun := restrictHom R U
  invFun := extendHom R U
  left_inv α := PresheafOfModules.hom_ext fun V ↦ by
    by_cases h : V.unop ≤ U
    · exact (dite_eq_left h).trans ((objIso R U F h).hom_inv_id_assoc (α.app V))
    · exact (isZero_obj R U F h).eq_of_src _ _
  right_inv α := PresheafOfModules.hom_ext fun V ↦
    (congrArg ((restrictObjIso R U F V).inv ≫ ·)
      (dite_eq_left (leOfHom V.unop.hom))).trans
      ((restrictObjIso R U F V).inv_hom_id_assoc (α.app V))

@[simp]
private lemma homEquiv_symm_apply_app {F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)}
    {G : PresheafOfModules.{v} R}
    (α : F ⟶ (PresheafOfModules.pushforward (F := Over.forget U)
      (𝟙 ((Over.forget U).op ⋙ R))).obj G)
    (V : Pᵒᵖ) : ((homEquiv R U F G).symm α).app V = extendApp R U α V :=
  rfl

/-- Extension by zero is left adjoint to restriction to the lower interval. -/
private def adjunction : functor R U ⊣
    PresheafOfModules.pushforward (F := Over.forget U) (𝟙 ((Over.forget U).op ⋙ R)) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv R U
      homEquiv_naturality_left_symm {F F' G} α β := PresheafOfModules.hom_ext fun V ↦ by
        by_cases h : V.unop ≤ U
        · let βV : _ ⟶ G.obj V := β.app (op (Over.mk (homOfLE h)))
          have hαβ : extendApp R U (α ≫ β) V = (objIso R U F h).hom ≫ α.app _ ≫ βV :=
            dite_eq_left h
          have hβ : extendApp R U β V = (objIso R U F' h).hom ≫ βV := dite_eq_left h
          simp [mapApp, h, hαβ, hβ]
        · exact (isZero_obj R U F h).eq_of_src _ _
      homEquiv_naturality_right α β :=
        PresheafOfModules.hom_ext fun _ ↦ (Category.assoc _ _ _).symm }

private instance evaluationPreservesFiniteLimits (V : Pᵒᵖ) :
    PreservesFiniteLimits (functor R U ⋙ PresheafOfModules.evaluation R V) := by
  by_cases h : V.unop ≤ U
  · exact preservesFiniteLimits_of_natIso (evaluationIso R U h).symm
  · have hz : IsZero (functor R U ⋙ PresheafOfModules.evaluation R V) :=
      (Functor.isZero_iff _).mpr fun F ↦ isZero_obj R U F h
    have := Functor.preservesLimitsOfSize_of_isZero _ hz
    infer_instance

private instance : PreservesFiniteLimits (functor R U) where
  preservesFiniteLimits _J _ _ :=
    { preservesLimit {_K} :=
        { preserves hc := ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _
            fun V ↦ isLimitOfPreserves (functor R U ⋙ PresheafOfModules.evaluation R V) hc⟩ } }

end ExtensionByZero

/-- Restriction of module presheaves to a lower interval has a left adjoint in arbitrary
module universes, given by extension by zero. -/
instance isRightAdjoint_pushforward_over :
    (PresheafOfModules.pushforward.{v} (F := Over.forget U)
      (𝟙 ((Over.forget U).op ⋙ R))).IsRightAdjoint :=
  (ExtensionByZero.adjunction R U).isRightAdjoint

/-- Extension by zero from a lower interval of a preorder preserves finite limits.
Together with its left adjoint structure, this makes extension by zero exact. -/
instance preservesFiniteLimits_pullback_over :
    PreservesFiniteLimits
      (PresheafOfModules.pullback.{v} (F := Over.forget U) (𝟙 ((Over.forget U).op ⋙ R))) :=
  preservesFiniteLimits_of_natIso
    ((ExtensionByZero.adjunction R U).leftAdjointUniq
      (PresheafOfModules.pullbackPushforwardAdjunction _))

end

end PresheafOfModules
