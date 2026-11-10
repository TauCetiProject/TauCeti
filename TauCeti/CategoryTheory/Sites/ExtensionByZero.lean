/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Extension by zero on a lower interval

For a preordered set `P` and `U : P`, a presheaf on `Over U` with values in a category with a
zero object extends to `P` by assigning zero outside the lower interval of `U`. This extension
preserves finite limits and colimits and is left adjoint to restriction. For the open subsets of
a space, sheafifying this construction gives extension by zero along an open inclusion.

The sheaf exactness instance supports the comparison of cohomology on an open with cohomology
of the restricted sheaf in `TauCeti.CategoryTheory.Sites.SheafCohomology.Over`.

## Main declarations

* `TauCeti.CategoryTheory.PresheafExtensionByZero.functor`: extension by zero of presheaves.
* `TauCeti.CategoryTheory.PresheafExtensionByZero.adjunction`: its adjunction to restriction.
* `TauCeti.CategoryTheory.SheafExtensionByZero.preservesFiniteLimits_sheafPullback`: left
  exactness of Mathlib's canonical extension functor for sheaves with values in a category with
  a zero object and finite limits.

## References

* R. Hartshorne, *Algebraic Geometry*, II, Exercise 1.19.
-/

public section

open CategoryTheory Limits Opposite ZeroObject

namespace TauCeti.CategoryTheory

universe u v w

noncomputable section

variable {P : Type u} [Preorder P] (U : P)

namespace PresheafExtensionByZero

variable {D : Type v} [Category.{w} D] [HasZeroObject D]

/-- The extension of a presheaf to an object of the ambient preorder. -/
private def obj (F : (Over U)ᵒᵖ ⥤ D) (V : Pᵒᵖ) : D := by
  classical
  exact if h : V.unop ≤ U then F.obj (op (Over.mk (homOfLE h))) else 0

/-- On an object below `U`, extension by zero recovers the original presheaf. -/
private def objIso (F : (Over U)ᵒᵖ ⥤ D) {V : Pᵒᵖ} (h : V.unop ≤ U) :
    obj U F V ≅ F.obj (op (Over.mk (homOfLE h))) :=
  eqToIso (dite_eq_left h)

private lemma isZero_obj (F : (Over U)ᵒᵖ ⥤ D) {V : Pᵒᵖ} (h : ¬ V.unop ≤ U) :
    IsZero (obj U F V) := by
  rw [obj, dite_eq_right h]
  exact isZero_zero _

variable [HasZeroMorphisms D]

private def map (F : (Over U)ᵒᵖ ⥤ D) {V W : Pᵒᵖ} (f : V ⟶ W) :
    obj U F V ⟶ obj U F W := by
  classical
  exact if hV : V.unop ≤ U then
    (objIso U F hV).hom ≫
      F.map (Over.homMk (U := Over.mk (homOfLE (le_trans (leOfHom f.unop) hV)))
        (V := Over.mk (homOfLE hV)) f.unop).op ≫
      (objIso U F (le_trans (leOfHom f.unop) hV)).inv
  else 0

/-- Extension by zero of a presheaf on the lower interval of `U`. -/
private def presheaf (F : (Over U)ᵒᵖ ⥤ D) : Pᵒᵖ ⥤ D where
  obj := obj U F
  map := map U F
  map_id V := by
    by_cases h : V.unop ≤ U
    · have hi : (Over.homMk (U := Over.mk (homOfLE h))
          (V := Over.mk (homOfLE h)) (𝟙 V.unop)).op = 𝟙 _ :=
        Quiver.Hom.unop_inj (Over.OverMorphism.ext (by simp))
      simp [map, objIso, obj, h, hi]
    · exact (isZero_obj U F h).eq_of_src _ _
  map_comp {V W Z} f g := by
    by_cases h : V.unop ≤ U
    · have hW := le_trans (leOfHom f.unop) h
      have hZ := le_trans (leOfHom g.unop) hW
      have hc : (Over.homMk (U := Over.mk (homOfLE hZ))
          (V := Over.mk (homOfLE h)) (g.unop ≫ f.unop)).op =
          (Over.homMk (U := Over.mk (homOfLE hW))
            (V := Over.mk (homOfLE h)) f.unop).op ≫
          (Over.homMk (U := Over.mk (homOfLE hZ))
            (V := Over.mk (homOfLE hW)) g.unop).op := by
        rw [← op_comp, ← Over.homMk_comp]
      simp [map, objIso, obj, h, hW, hc]
    · simp [map, h]

private def mapApp {F G : (Over U)ᵒᵖ ⥤ D} (α : F ⟶ G) (V : Pᵒᵖ) :
    obj U F V ⟶ obj U G V := by
  classical
  exact if h : V.unop ≤ U then
    (objIso U F h).hom ≫ α.app (op (Over.mk (homOfLE h))) ≫ (objIso U G h).inv
  else 0

/-- Extension by zero as a functor between categories of presheaves. -/
def functor : ((Over U)ᵒᵖ ⥤ D) ⥤ (Pᵒᵖ ⥤ D) where
  obj := presheaf U
  map α :=
    { app := mapApp U α
      naturality V W f := by
        by_cases hV : V.unop ≤ U
        · have hW := le_trans (leOfHom f.unop) hV
          simp [presheaf, map, mapApp, hV, hW]
        · simp [presheaf, map, mapApp, hV] }
  map_id F := by
    ext V
    by_cases h : V.unop ≤ U
    · simp [presheaf, mapApp, h]
    · exact (isZero_obj U F h).eq_of_src _ _
  map_comp α β := by
    ext V
    by_cases h : V.unop ≤ U <;> simp [presheaf, mapApp, h]

/-- Evaluating the extension below `U` is naturally isomorphic to evaluating the original
presheaf. -/
def evaluationIso {V : P} (h : V ≤ U) :
    functor (D := D) U ⋙ (evaluation Pᵒᵖ D).obj (op V) ≅
      (evaluation (Over U)ᵒᵖ D).obj (op (Over.mk (homOfLE h))) :=
  NatIso.ofComponents (fun F ↦ objIso U F h) fun α ↦ by
    simp [functor, presheaf, mapApp, h]

private lemma evaluationIso_hom_app (F : (Over U)ᵒᵖ ⥤ D) {V : P} (h : V ≤ U) :
    (evaluationIso U h).hom.app F = (objIso U F h).hom :=
  rfl

/-- The identification `evaluationIso` is compatible with restriction maps below `U`. -/
@[reassoc]
theorem map_comp_evaluationIso_hom_app (F : (Over U)ᵒᵖ ⥤ D) {V W : P} (hWV : W ≤ V)
    (hV : V ≤ U) :
    ((functor U).obj F).map (homOfLE hWV).op ≫ (evaluationIso U (hWV.trans hV)).hom.app F =
      (evaluationIso U hV).hom.app F ≫
        F.map (Over.homMk (U := Over.mk (homOfLE (hWV.trans hV)))
          (V := Over.mk (homOfLE hV)) (homOfLE hWV)).op := by
  simp [evaluationIso_hom_app, functor, presheaf, map, hV]

/-- Extension by zero vanishes outside the lower interval. -/
theorem isZero_obj_of_not_le (F : (Over U)ᵒᵖ ⥤ D) {V : P}
    (h : ¬ V ≤ U) : IsZero ((functor (D := D) U).obj F |>.obj (op V)) := by
  dsimp only [functor, presheaf]
  exact isZero_obj U F h

private lemma isZero_functor_comp_evaluation {V : P} (h : ¬ V ≤ U) :
    IsZero (functor (D := D) U ⋙ (evaluation Pᵒᵖ D).obj (op V)) :=
  (Functor.isZero_iff _).mpr fun F ↦ isZero_obj_of_not_le U F h

/-- Extension by zero preserves finite limits. -/
instance [HasFiniteLimits D] : PreservesFiniteLimits (functor (D := D) U) :=
  preservesFiniteLimits_of_evaluation _ fun V ↦ by
    by_cases h : V.unop ≤ U
    · exact preservesFiniteLimits_of_natIso (evaluationIso U h).symm
    · have :=
        Functor.preservesLimitsOfSize_of_isZero _ (isZero_functor_comp_evaluation (D := D) U h)
      infer_instance

/-- Extension by zero preserves finite colimits. -/
instance [HasFiniteColimits D] : PreservesFiniteColimits (functor (D := D) U) :=
  preservesFiniteColimits_of_evaluation _ fun V ↦ by
    by_cases h : V.unop ≤ U
    · exact preservesFiniteColimits_of_natIso (evaluationIso U h).symm
    · have :=
        Functor.preservesColimitsOfSize_of_isZero _ (isZero_functor_comp_evaluation (D := D) U h)
      infer_instance

private def restrictObjIso (F : (Over U)ᵒᵖ ⥤ D) (V : (Over U)ᵒᵖ) :
    obj U F (op V.unop.left) ≅ F.obj V :=
  objIso U F (leOfHom V.unop.hom)

private def restrictHom {F : (Over U)ᵒᵖ ⥤ D} {G : Pᵒᵖ ⥤ D}
    (α : presheaf U F ⟶ G) : F ⟶ (Over.forget U).op ⋙ G where
  app V := (restrictObjIso U F V).inv ≫ α.app (op V.unop.left)
  naturality V W f := by
    have h := α.naturality ((Over.forget U).op.map f)
    simp only [presheaf, map, Functor.op_obj, Over.forget_obj, dite_eq_left (leOfHom V.unop.hom),
      Category.assoc] at h
    -- `h` restates the goal with `Over.mk (homOfLE (leOfHom X.hom))` for `X`; these agree
    -- by structure eta and proof irrelevance.
    exact ((Iso.eq_inv_comp _).mpr h).trans (Category.assoc _ _ _).symm

private def extendApp {F : (Over U)ᵒᵖ ⥤ D} {G : Pᵒᵖ ⥤ D}
    (α : F ⟶ (Over.forget U).op ⋙ G) (V : Pᵒᵖ) : obj U F V ⟶ G.obj V := by
  classical
  exact if h : V.unop ≤ U then (objIso U F h).hom ≫ α.app (op (Over.mk (homOfLE h)))
    else 0

private def extendHom {F : (Over U)ᵒᵖ ⥤ D} {G : Pᵒᵖ ⥤ D}
    (α : F ⟶ (Over.forget U).op ⋙ G) : presheaf U F ⟶ G where
  app := extendApp U α
  naturality V W f := by
    by_cases hV : V.unop ≤ U
    · have hW := le_trans (leOfHom f.unop) hV
      simp [presheaf, map, extendApp, hV, hW]
    · simp [presheaf, map, extendApp, hV]

/-- Extension by zero is left adjoint to restriction to the lower interval. -/
def adjunction : functor (D := D) U ⊣
    (Functor.whiskeringLeft (Over U)ᵒᵖ Pᵒᵖ D).obj (Over.forget U).op :=
  Adjunction.mkOfHomEquiv
    { homEquiv F G :=
        { toFun := restrictHom U
          invFun := extendHom U
          left_inv α := by
            ext V
            by_cases h : V.unop ≤ U
            · dsimp only [extendHom, restrictHom]
              simp only [extendApp, dite_eq_left h, restrictObjIso]
              exact (objIso U F h).hom_inv_id_assoc (α.app V)
            · exact (isZero_obj_of_not_le U F h).eq_of_src _ _
          right_inv α := by
            ext V
            dsimp only [restrictHom, extendHom]
            simp only [extendApp, dite_eq_left (leOfHom V.unop.hom), restrictObjIso]
            exact (objIso U F (V := op V.unop.left) (leOfHom V.unop.hom)).inv_hom_id_assoc
              (α.app V) }
      homEquiv_naturality_left_symm := by
        intro F F' G α β
        -- Unfold the `Equiv.mk` above and read `presheaf U F` as `(functor U).obj F`. The two
        -- agree only by unfolding `functor`, so `simp` cannot rewrite the application.
        change extendHom U (α ≫ β) = (functor (D := D) U).map α ≫ extendHom U β
        ext V
        by_cases h : V.unop ≤ U
        · simp [extendHom, extendApp, functor, mapApp, presheaf, h]
        · exact (isZero_obj_of_not_le U F h).eq_of_src _ _
      homEquiv_naturality_right α β := by
        ext V
        exact (Category.assoc _ _ _).symm }

end PresheafExtensionByZero

namespace SheafExtensionByZero

variable {D : Type v} [Category.{w} D] [HasZeroObject D] [HasZeroMorphisms D]
  (J : GrothendieckTopology P) [HasSheafify J D]

private def extension : Sheaf (J.over U) D ⥤ Sheaf J D :=
  sheafToPresheaf (J.over U) _ ⋙ PresheafExtensionByZero.functor U ⋙ presheafToSheaf J _

private def extensionAdjunction : extension U J ⊣ J.overPullback D U :=
  ((PresheafExtensionByZero.adjunction U).comp (sheafificationAdjunction J D)).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf (J.over U) _) (Functor.FullyFaithful.id _)
    (Iso.refl _) (Iso.refl _)

/-- On a preorder site, restriction to a lower interval has a left adjoint. -/
instance isRightAdjoint_sheafPushforwardContinuous_forget :
    ((Over.forget U).sheafPushforwardContinuous D (J.over U) J).IsRightAdjoint :=
  (extensionAdjunction U J).isRightAdjoint

variable [HasFiniteLimits D]

private instance : PreservesFiniteLimits (extension (D := D) U J) := by
  unfold extension
  infer_instance

/-- On a preorder site, the left adjoint to restriction to a lower interval is exact.
In particular, this applies to extension by zero along an open inclusion. -/
instance preservesFiniteLimits_sheafPullback :
    PreservesFiniteLimits ((Over.forget U).sheafPullback D (J.over U) J) :=
  preservesFiniteLimits_of_natIso
    ((extensionAdjunction U J).leftAdjointUniq
      ((Over.forget U).sheafAdjunctionContinuous D (J.over U) J))

end SheafExtensionByZero

end

end TauCeti.CategoryTheory
