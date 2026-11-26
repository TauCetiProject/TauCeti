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
  NatIso.ofComponents (fun X ↦
    let I := injectiveResolution X
    ((ev).obj j).mapIso (I.isoRightDerivedObj F n) ≪≫
      (((ev).obj j).mapHomologicalComplexCompHomologyFunctorIso _ n).symm.app
        ((F.mapHomologicalComplex _).obj I.cocomplex) ≪≫
      (I.isoRightDerivedObj (F ⋙ (ev).obj j) n).symm)
    (fun {X Y} f ↦ by
      let I := injectiveResolution X
      let K := injectiveResolution Y
      let φ := InjectiveResolution.desc f K I
      have hφ := InjectiveResolution.desc_commutes_zero f K I
      simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom,
        Category.assoc, Functor.comp_map]
      rw [← Functor.map_comp_assoc ((ev).obj j),
        InjectiveResolution.isoRightDerivedObj_hom_naturality f I K φ hφ F n,
        Functor.map_comp, Category.assoc,
        InjectiveResolution.isoRightDerivedObj_inv_naturality f I K φ hφ (F ⋙ (ev).obj j) n]
      exact congrArg (((ev).obj j).map (I.isoRightDerivedObj F n).hom ≫ ·)
        ((((ev).obj j).mapHomologicalComplexCompHomologyFunctorIso _ n).inv.naturality_assoc
          ((F.mapHomologicalComplex _).map φ) _))

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
  simp only [rightDerivedEvaluationIso, NatTrans.comp_app, Functor.whiskerLeft_app,
    NatIso.ofComponents_hom_app, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc]
  simp only [evaluation_obj_map, evaluation_map_app]
  rw [← Category.assoc, hn, Category.assoc, hr, Iso.inv_hom_id_assoc]
  refine congrArg (fun g ↦ (I.isoRightDerivedObj F n).hom.app i ≫ g) ?_
  rw [Functor.mapHomologicalComplexCompHomologyFunctorIso_inv_app,
    Functor.mapHomologicalComplexCompHomologyFunctorIso_inv_app]
  have h := NatTrans.app_homology ((ev).map f) (K.sc n)
  simp only [evaluation_map_app] at h
  calc
    _ = (K.sc n).homology.map f ≫ ((K.sc n).mapHomologyIso ((ev).obj j)).inv ≫
        (I.isoRightDerivedObj (F ⋙ (ev).obj j) n).inv := rfl
    _ = _ := by
      simp only [h, Category.assoc, Iso.hom_inv_id_assoc]
      -- Both maps come from evaluating each term of the same cochain complex along `f`.
      rfl

end CategoryTheory
