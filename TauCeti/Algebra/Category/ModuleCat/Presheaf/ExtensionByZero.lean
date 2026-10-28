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

/-- The extension of a presheaf to an object of the ambient preorder. -/
private def obj (F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)) (V : Pᵒᵖ) :
    ModuleCat.{v} (R.obj V) := by
  classical
  exact if h : V.unop ≤ U then F.obj (op (Over.mk (homOfLE h))) else 0

/-- On an object below `U`, extension by zero recovers the original presheaf. -/
private def objIso (F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)) {V : Pᵒᵖ} (h : V.unop ≤ U) :
    obj R U F V ≅ F.obj (op (Over.mk (homOfLE h))) := by
  classical
  exact eqToIso (by simp [obj, h])

private def map (F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)) {V W : Pᵒᵖ} (f : V ⟶ W) :
    obj R U F V ⟶ (ModuleCat.restrictScalars (R.map f).hom).obj (obj R U F W) := by
  classical
  exact if hV : V.unop ≤ U then
    (objIso R U F hV).hom ≫
      F.map (Over.homMk (U := Over.mk (homOfLE (le_trans (leOfHom f.unop) hV)))
        (V := Over.mk (homOfLE hV)) f.unop).op ≫
      (ModuleCat.restrictScalars (R.map f).hom).map
        (objIso R U F (le_trans (leOfHom f.unop) hV)).inv
  else 0

private lemma map_apply (F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R))
    {V W : Pᵒᵖ} (f : V ⟶ W) (hV : V.unop ≤ U) (x : obj R U F V) :
    map R U F f x = (objIso R U F (le_trans (leOfHom f.unop) hV)).inv
      (F.map (Over.homMk (U := Over.mk (homOfLE (le_trans (leOfHom f.unop) hV)))
        (V := Over.mk (homOfLE hV)) f.unop).op ((objIso R U F hV).hom x)) := by
  classical
  rw [map, dite_eq_left hV]
  rfl

/-- Extension by zero of a presheaf on the lower interval of `U`. -/
private def presheaf (F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)) :
    PresheafOfModules.{v} R where
  obj := obj R U F
  map := map R U F
  map_id V := by
    classical
    by_cases h : V.unop ≤ U
    · ext x
      -- Scalar restriction along an identity ring map is the identity on elements.
      change map R U F (𝟙 V) x = x
      erw [map_apply R U F _ h]
      have hi : (Over.homMk (U := Over.mk (homOfLE h))
          (V := Over.mk (homOfLE h)) (𝟙 V).unop).op = 𝟙 _ := by
        apply Quiver.Hom.op_inj
        ext
        rfl
      rw [hi, F.map_id]
      change (objIso R U F h).inv ((objIso R U F h).hom x) = x
      exact (objIso R U F h).toLinearEquiv.symm_apply_apply x
    · have hz : IsZero (obj R U F V) := by
        rw [obj, dite_eq_right h]
        exact isZero_zero _
      exact hz.eq_of_src _ _
  map_comp {V W Z} f g := by
    classical
    by_cases h : V.unop ≤ U
    · ext x
      -- The scalar-composition comparison also acts identically on elements.
      change map R U F (f ≫ g) x = map R U F g (map R U F f x)
      have hW := le_trans (leOfHom f.unop) h
      have hZ := le_trans (leOfHom g.unop) hW
      erw [map_apply R U F _ h, map_apply R U F _ hW, map_apply R U F _ h]
      have hc : (Over.homMk (U := Over.mk (homOfLE hZ))
          (V := Over.mk (homOfLE h)) (f ≫ g).unop).op =
          (Over.homMk (U := Over.mk (homOfLE hW))
            (V := Over.mk (homOfLE h)) f.unop).op ≫
          (Over.homMk (U := Over.mk (homOfLE hZ))
            (V := Over.mk (homOfLE hW)) g.unop).op := by
        apply Quiver.Hom.op_inj
        ext
        rfl
      erw [hc, F.map_comp_apply]
      congr 2
      exact ((objIso R U F hW).toLinearEquiv.apply_symm_apply _).symm
    · simp only [map, dite_eq_right h]
      exact zero_comp.symm

private def mapApp {F G : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)} (α : F ⟶ G) (V : Pᵒᵖ) :
    obj R U F V ⟶ obj R U G V := by
  classical
  exact if h : V.unop ≤ U then
    (objIso R U F h).hom ≫ α.app (op (Over.mk (homOfLE h))) ≫ (objIso R U G h).inv
  else 0

private lemma mapApp_apply {F G : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)}
    (α : F ⟶ G) (V : Pᵒᵖ) (h : V.unop ≤ U) (x : obj R U F V) :
    mapApp R U α V x = (objIso R U G h).inv
      (α.app (op (Over.mk (homOfLE h))) ((objIso R U F h).hom x)) := by
  classical
  rw [mapApp, dite_eq_left h]
  rfl

/-- Extension by zero as a functor between categories of presheaves. -/
private def functor : PresheafOfModules.{v} ((Over.forget U).op ⋙ R) ⥤ PresheafOfModules.{v} R where
  obj := presheaf R U
  map {F G} α :=
    { app := mapApp R U α
      naturality := by
        intro V W f
        classical
        by_cases hV : V.unop ≤ U
        · have hW := le_trans (leOfHom f.unop) hV
          ext x
          -- Work on elements to preserve the dependent scalar-ring presentations;
          -- the linear equivalences expose the inverse laws of the fiber comparisons.
          change mapApp R U α W (map R U _ f x) =
            map R U _ f (mapApp R U α V x)
          erw [mapApp_apply R U α _ hW, map_apply R U _ _ hV,
            map_apply R U _ _ hV, mapApp_apply R U α _ hV]
          change (objIso R U _ hW).inv _ = (objIso R U _ hW).inv _
          congr 1
          change α.app _ ((objIso R U _ hW).toLinearEquiv
            ((objIso R U _ hW).toLinearEquiv.symm _)) =
            G.map _ ((objIso R U _ hV).toLinearEquiv
              ((objIso R U _ hV).toLinearEquiv.symm _))
          erw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
          exact PresheafOfModules.naturality_apply α _ _
        · simp [presheaf, map, mapApp, hV] }
  map_id F := by
    apply PresheafOfModules.hom_ext
    intro V
    classical
    dsimp only [presheaf, NatTrans.id_app]
    by_cases h : V.unop ≤ U
    · simp [mapApp, h]
    · have hz : IsZero (obj R U F V) := by
        erw [obj, dite_eq_right h]
        exact isZero_zero _
      exact hz.eq_of_src _ _
  map_comp α β := by
    apply PresheafOfModules.hom_ext
    intro V
    classical
    dsimp only [presheaf, NatTrans.comp_app]
    by_cases h : V.unop ≤ U <;> simp [mapApp, h, Category.assoc]

/-- Evaluating the extension below `U` is naturally isomorphic to evaluating the original
presheaf. -/
private def evaluationIso {V : P} (h : V ≤ U) :
    functor R U ⋙ PresheafOfModules.evaluation R (op V) ≅
      PresheafOfModules.evaluation ((Over.forget U).op ⋙ R) (op (Over.mk (homOfLE h))) :=
  NatIso.ofComponents (fun F ↦ objIso R U F h) (by
    intro F G α
    classical
    -- Evaluation only changes the presentation of the component module map.
    change mapApp R U α (op V) ≫ (objIso R U G h).hom =
      (objIso R U F h).hom ≫ α.app _
    simp [mapApp, h, Category.assoc])

/-- Extension by zero vanishes outside the lower interval. -/
private theorem isZero_obj_of_not_le (F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)) {V : P}
    (h : ¬ V ≤ U) : IsZero ((functor R U).obj F |>.obj (op V)) := by
  classical
  dsimp only [functor, presheaf]
  erw [obj, dite_eq_right h]
  exact isZero_zero _

private def restrictObjIso (F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)) (V : (Over U)ᵒᵖ) :
    obj R U F (op V.unop.left) ≅ F.obj V :=
  objIso R U F (leOfHom V.unop.hom)

private def restrictHom {F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)}
    {G : PresheafOfModules.{v} R}
    (α : presheaf R U F ⟶ G) :
    F ⟶ (PresheafOfModules.pushforward (F := Over.forget U)
      (𝟙 ((Over.forget U).op ⋙ R))).obj G where
  app V := (restrictObjIso R U F V).inv ≫ α.app (op V.unop.left)
  naturality {V W} f := by
    classical
    ext x
    -- Forget the scalar-restriction wrappers and compare the two section maps.
    -- The fiber equivalence cancels the extension/restriction identification.
    change α.app (op W.unop.left) ((restrictObjIso R U F W).inv (F.map f x)) =
      G.map ((Over.forget U).op.map f)
        (α.app (op V.unop.left) ((restrictObjIso R U F V).inv x))
    have h := PresheafOfModules.naturality_apply α ((Over.forget U).op.map f)
      ((restrictObjIso R U F V).inv x)
    change α.app (op W.unop.left)
      (map R U F ((Over.forget U).op.map f) ((restrictObjIso R U F V).inv x)) =
      G.map ((Over.forget U).op.map f)
        (α.app (op V.unop.left) ((restrictObjIso R U F V).inv x)) at h
    erw [map_apply R U F _ (leOfHom V.unop.hom)] at h
    have hf : (Over.homMk (U := W.unop) (V := V.unop) f.unop.left).op = f := by
      rw [Over.homMk_eta]
      rfl
    change α.app _ ((restrictObjIso R U F W).inv
      (F.map (Over.homMk (U := W.unop) (V := V.unop) f.unop.left).op
        ((restrictObjIso R U F V).toLinearEquiv
          ((restrictObjIso R U F V).toLinearEquiv.symm x)))) = _ at h
    erw [LinearEquiv.apply_symm_apply, hf] at h
    exact h

private def extendApp {F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)}
    {G : PresheafOfModules.{v} R}
    (α : F ⟶ (PresheafOfModules.pushforward (F := Over.forget U)
      (𝟙 ((Over.forget U).op ⋙ R))).obj G) (V : Pᵒᵖ) : obj R U F V ⟶ G.obj V := by
  classical
  exact if h : V.unop ≤ U then (objIso R U F h).hom ≫ α.app (op (Over.mk (homOfLE h)))
    else 0

private def extendHom {F : PresheafOfModules.{v} ((Over.forget U).op ⋙ R)}
    {G : PresheafOfModules.{v} R}
    (α : F ⟶ (PresheafOfModules.pushforward (F := Over.forget U)
      (𝟙 ((Over.forget U).op ⋙ R))).obj G) : presheaf R U F ⟶ G where
  app := extendApp R U α
  naturality {V W} f := by
    classical
    ext x
    -- Scalar restrictions act identically on elements, so the original module
    -- naturality equation applies after cancelling the fiber equivalence.
    change extendApp R U α W (map R U F f x) = G.map f (extendApp R U α V x)
    by_cases hV : V.unop ≤ U
    · have hW := le_trans (leOfHom f.unop) hV
      erw [extendApp, dite_eq_left hW, extendApp, dite_eq_left hV,
        map_apply R U F _ hV]
      change α.app _ ((objIso R U F hW).toLinearEquiv
        ((objIso R U F hW).toLinearEquiv.symm _)) = _
      erw [LinearEquiv.apply_symm_apply]
      exact PresheafOfModules.naturality_apply α _ _
    · have he : extendApp R U α V = 0 := by rw [extendApp, dite_eq_right hV]
      erw [map, dite_eq_right hV, he]
      change extendApp R U α W 0 = G.map f 0
      exact (extendApp R U α W).hom.map_zero.trans (G.map f).hom.map_zero.symm

/-- Extension by zero is left adjoint to restriction to the lower interval. -/
private def adjunction : functor R U ⊣
    PresheafOfModules.pushforward (F := Over.forget U) (𝟙 ((Over.forget U).op ⋙ R)) :=
  Adjunction.mkOfHomEquiv
    { homEquiv F G :=
        { toFun := restrictHom R U
          invFun := extendHom R U
          left_inv α := by
            apply PresheafOfModules.hom_ext
            intro V
            classical
            by_cases h : V.unop ≤ U
            · dsimp only [extendHom, restrictHom]
              simp only [extendApp, dite_eq_left h, restrictObjIso]
              exact (objIso R U F h).hom_inv_id_assoc (α.app V)
            · exact (isZero_obj_of_not_le R U F h).eq_of_src _ _
          right_inv α := by
            apply PresheafOfModules.hom_ext
            intro V
            classical
            dsimp only [restrictHom, extendHom]
            simp only [extendApp, dite_eq_left (leOfHom V.unop.hom), restrictObjIso]
            exact (objIso R U F (V := op V.unop.left) (leOfHom V.unop.hom)).inv_hom_id_assoc
              (α.app V) }
      homEquiv_naturality_left_symm := by
        intro F F' G α β
        -- Read the hom-equivalence as extension of module maps. The component
        -- comparison then reduces to the inverse law of the intermediate fiber.
        change extendHom R U (α ≫ β) = (functor R U).map α ≫ extendHom R U β
        apply PresheafOfModules.hom_ext
        intro V
        classical
        by_cases h : V.unop ≤ U
        · ext x
          change extendApp R U (α ≫ β) V x =
            extendApp R U β V (mapApp R U α V x)
          erw [extendApp, dite_eq_left h, extendApp, dite_eq_left h,
            mapApp_apply R U α V h]
          change β.app _ (α.app _ ((objIso R U F h).hom x)) =
            β.app _ ((objIso R U F' h).toLinearEquiv
              ((objIso R U F' h).toLinearEquiv.symm _))
          exact (congrArg (β.app _)
            ((objIso R U F' h).toLinearEquiv.apply_symm_apply _)).symm
        · exact (isZero_obj_of_not_le R U F h).eq_of_src _ _
      homEquiv_naturality_right := by
        intro F G G' α β
        apply PresheafOfModules.hom_ext
        intro V
        exact (Category.assoc _ _ _).symm }

private instance evaluationPreservesFiniteLimits (V : Pᵒᵖ) :
    PreservesFiniteLimits (functor R U ⋙ PresheafOfModules.evaluation R V) := by
  classical
  by_cases h : V.unop ≤ U
  · exact preservesFiniteLimits_of_natIso (evaluationIso R U h).symm
  · have hz : IsZero (functor R U ⋙ PresheafOfModules.evaluation R V) :=
      (Functor.isZero_iff _).mpr (fun F ↦ isZero_obj_of_not_le R U F h)
    have := Functor.preservesLimitsOfSize_of_isZero _ hz
    infer_instance

private instance : PreservesFiniteLimits (functor R U) where
  preservesFiniteLimits _J _ _ :=
    { preservesLimit {_K} :=
        { preserves hc := ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _
            (fun V ↦ isLimitOfPreserves (functor R U ⋙ PresheafOfModules.evaluation R V) hc)⟩ } }

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
