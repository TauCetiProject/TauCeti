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
  Functor.rightDerivedCompIso F ((ev).obj j) (𝟭 C) (F ⋙ (ev).obj j)
    (Functor.leftUnitor _).symm n ≪≫ Functor.leftUnitor _

/-- On an injective resolution, evaluation commutes with cohomology by exactness. -/
@[reassoc]
lemma Functor.rightDerivedEvaluationIso_hom_app_injectiveResolution (n : ℕ) (j : J)
    {X : C} (I : InjectiveResolution X) :
    (F.rightDerivedEvaluationIso n j).hom.app X =
      ((ev).obj j).map (I.isoRightDerivedObj F n).hom ≫
        (((ev).obj j).mapHomologicalComplexCompHomologyFunctorIso _ n).inv.app
          ((F.mapHomologicalComplex _).obj I.cocomplex) ≫
        (I.isoRightDerivedObj (F ⋙ (ev).obj j) n).inv := by
  let G := F ⋙ (ev).obj j
  let J₀ := (𝟭 C).mapInjectiveResolution I
  let c := ComplexShape.up ℕ
  have hcomp :
      ((Functor.mapHomologicalComplexCompIso (Functor.leftUnitor G).symm c).app I.cocomplex ≪≫
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (𝟭 C ⋙ G)) c).app I.cocomplex).symm).hom =
        𝟙 ((G.mapHomologicalComplex c).obj I.cocomplex) := by
    ext k
    simp only [Iso.trans_hom, HomologicalComplex.comp_f, Iso.app_hom, Iso.symm_hom, Iso.app_inv,
      mapHomologicalComplexCompIso_hom_app_f, mapHomologicalComplexCompIso_inv_app_f,
      Functor.leftUnitor_inv_app, Iso.refl_inv, NatTrans.id_app,
      HomologicalComplex.id_f]
    exact Category.id_comp _
  have hres : (J₀.isoRightDerivedObj G n).inv = (I.isoRightDerivedObj G n).inv := by
    have h := I.isoRightDerivedObj_inv_naturality (𝟙 X) J₀ (𝟙 I.cocomplex)
      (by
        rw [HomologicalComplex.id_f, Functor.mapInjectiveResolution_ι_f_zero, Functor.id_map]
        -- The degree-zero object of the single complex is X, and the identity functor
        -- leaves the resolution complex unchanged.
        exact (Category.comp_id _).trans (Category.id_comp _).symm) G n
    -- Use the map-of-identity laws on each side of the resolution naturality square.
    refine ((Category.id_comp _).symm.trans
      (congrArg (· ≫ (J₀.isoRightDerivedObj G n).inv)
        ((G.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor D _ n).map_id
          I.cocomplex).symm)).trans (h.symm.trans ?_)
    exact (congrArg ((I.isoRightDerivedObj G n).inv ≫ ·)
      ((G.rightDerived n).map_id X)).trans (Category.comp_id _)
  rw [← Iso.app_hom]
  rw [rightDerivedEvaluationIso, NatIso.trans_app,
    Functor.rightDerivedCompIso_app_injectiveResolution F ((ev).obj j) (𝟭 C) G _ I]
  -- The identity precomposition leaves the evaluated complex unchanged. Unification
  -- identifies the two presentations of this complex when applying hcomp.
  refine (Category.comp_id _).trans (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) ?_))
  exact (congrArg (fun k ↦ (HomologicalComplex.homologyFunctor D c n).map k ≫
      (J₀.isoRightDerivedObj G n).inv) hcomp).trans
    ((congrArg (· ≫ (J₀.isoRightDerivedObj G n).inv)
      ((HomologicalComplex.homologyFunctor D c n).map_id _)).trans
    ((Category.id_comp _).trans hres))

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
