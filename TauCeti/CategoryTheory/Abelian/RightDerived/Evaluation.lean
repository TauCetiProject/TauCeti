/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import TauCeti.CategoryTheory.Abelian.RightDerived

/-!
# Evaluation of diagram-valued right derived functors

For a functor with values in a diagram category, evaluating its right derived functor at an
index gives the right derived functor of the evaluation. This comparison is natural in the
index, so it identifies the arrows in the diagram of cohomology with the derived arrows.
-/

public section

namespace CategoryTheory

open Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type*} [Category* D] [Abelian D]

variable {J : Type*} [Category* J] (F : C ⥤ J ⥤ D) [F.Additive]

local notation "ev" => evaluation J D

/-- Evaluating a diagram-valued right derived functor agrees with deriving its evaluation. -/
noncomputable def Functor.rightDerivedEvaluationIso (n : ℕ) (j : J) :
    F.rightDerived n ⋙ (ev).obj j ≅ (F ⋙ (ev).obj j).rightDerived n :=
  F.rightDerivedPostcompIso ((ev).obj j) n

/-- On an injective resolution, evaluation commutes with cohomology by exactness. -/
@[reassoc]
lemma Functor.rightDerivedEvaluationIso_hom_app_injectiveResolution (n : ℕ) (j : J)
    {X : C} (I : InjectiveResolution X) :
    (F.rightDerivedEvaluationIso n j).hom.app X =
      ((ev).obj j).map (I.isoRightDerivedObj F n).hom ≫
        (((ev).obj j).mapHomologicalComplexCompHomologyFunctorIso _ n).inv.app
          ((F.mapHomologicalComplex _).obj I.cocomplex) ≫
        (I.isoRightDerivedObj (F ⋙ (ev).obj j) n).inv :=
  F.rightDerivedPostcompIso_hom_app_injectiveResolution ((ev).obj j) I n

private lemma homologyFunctor_map_evaluation (K : HomologicalComplex (J ⥤ D) (.up ℕ))
    (n : ℕ) {i j : J} (f : i ⟶ j) :
    (HomologicalComplex.homologyFunctor D (.up ℕ) n).map
        ((((ev).map f).mapHomologicalComplex (.up ℕ)).app K) =
      ShortComplex.homologyMap ((K.sc n).mapNatTrans ((ev).map f)) := by
  rw [HomologicalComplex.homologyFunctor_map, HomologicalComplex.homologyMap]
  congr 1

/-- The evaluation comparison is natural in the indexing category of the diagrams. -/
@[reassoc]
lemma Functor.rightDerivedEvaluationIso_hom_naturality (n : ℕ) {i j : J} (f : i ⟶ j) :
    Functor.whiskerLeft (F.rightDerived n) ((ev).map f) ≫
        (F.rightDerivedEvaluationIso n j).hom =
      (F.rightDerivedEvaluationIso n i).hom ≫
        (Functor.whiskerLeft F ((ev).map f)).rightDerived n := by
  apply NatTrans.ext
  funext X
  let I := injectiveResolution X
  let K := (F.mapHomologicalComplex _).obj I.cocomplex
  have hn := (I.isoRightDerivedObj F n).hom.naturality f
  have hr := InjectiveResolution.rightDerived_app_eq (Functor.whiskerLeft F ((ev).map f)) I n
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    F.rightDerivedEvaluationIso_hom_app_injectiveResolution n i I,
    F.rightDerivedEvaluationIso_hom_app_injectiveResolution n j I, Category.assoc]
  simp only [evaluation_obj_map, evaluation_map_app]
  rw [← Category.assoc, hn, Category.assoc, hr, Iso.inv_hom_id_assoc]
  refine congrArg (fun g ↦ (I.isoRightDerivedObj F n).hom.app i ≫ g) ?_
  rw [Functor.mapHomologicalComplexCompHomologyFunctorIso_inv_app,
    Functor.mapHomologicalComplexCompHomologyFunctorIso_inv_app]
  have hmap :
      (HomologicalComplex.homologyFunctor D (.up ℕ) n).map
          (((Functor.whiskerLeft F ((ev).map f)).mapHomologicalComplex (.up ℕ)).app
            I.cocomplex) =
        ShortComplex.homologyMap ((K.sc n).mapNatTrans ((ev).map f)) :=
    homologyFunctor_map_evaluation K n f
  have h := NatTrans.app_homology ((ev).map f) (K.sc n)
  simp only [evaluation_map_app] at h
  simp only [HomologicalComplex.homologyFunctor_obj, HomologicalComplex.homology]
  dsimp only [K] at h hmap
  rw [hmap, reassoc_of% h, Iso.hom_inv_id_assoc]

end CategoryTheory
