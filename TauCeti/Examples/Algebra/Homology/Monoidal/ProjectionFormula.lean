/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.ProjectionFormula
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# Checks of the cochain projection formula

The identity projection formula on abelian groups induces the identity comparison on
unbounded complexes and preserves K-flatness. For two single complexes in arbitrary
integer degrees, the comparison has the expected value on the supported tensor summand.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

namespace TauCeti.Examples.CochainProjectionFormula

/-- The ordinary projection formula for the identity functors used in these checks. -/
private def identityProjectionFormula :
    (𝟭 (ModuleCat ℤ)).prod (𝟭 _) ⋙ tensor (ModuleCat ℤ) ⋙ (𝟭 _) ≅
      (𝟭 (ModuleCat ℤ)).prod (𝟭 _) ⋙ tensor (ModuleCat ℤ) :=
  Functor.isoWhiskerLeft _ (Functor.rightUnitor _)

private lemma identityProjectionFormula_hom_app (X Y : ModuleCat ℤ) :
    identityProjectionFormula.hom.app (X, Y) = 𝟙 (X ⊗ Y) := by
  simp only [identityProjectionFormula, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.comp_obj, Functor.prod_obj,
    Functor.id_obj, tensor_obj]

private lemma identityProjectionFormula_inv_app (X Y : ModuleCat ℤ) :
    identityProjectionFormula.inv.app (X, Y) = 𝟙 (X ⊗ Y) := by
  simp only [identityProjectionFormula, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.rightUnitor_inv_app, Functor.comp_obj, Functor.prod_obj,
    Functor.id_obj, tensor_obj]

/-- On abelian-group complexes, the identity projection formula agrees with the native
identity-functor comparison. -/
theorem _root_.HomologicalComplex.projectionFormulaHomologicalComplexIso_id_hom
    (K E : CochainComplex (ModuleCat ℤ) ℤ) :
    let t := Functor.mapHomologicalComplexIdIso (ModuleCat ℤ) (.up ℤ)
    ((𝟭 (ModuleCat ℤ)).projectionFormulaHomologicalComplexIso (𝟭 _)
      (Functor.isoWhiskerLeft _ (Functor.rightUnitor _)) K E).hom ≫
        tensorHom (𝟙 K) (t.hom.app E) =
      t.hom.app _ ≫ tensorHom (t.hom.app K) (𝟙 E) := by
  dsimp only
  rw [← identityProjectionFormula]
  apply (cancel_epi
    ((𝟭 (ModuleCat ℤ)).projectionFormulaHomologicalComplexIso (𝟭 _)
      identityProjectionFormula K E).inv).1
  rw [Iso.inv_hom_id_assoc]
  apply Hom.ext
  funext n
  refine mapBifunctor.hom_ext fun p q hpq ↦ ?_
  simp only [comp_f, ι_tensorHom, Functor.ι_projectionFormulaHomologicalComplexIso_inv_f_assoc,
    Functor.mapHomologicalComplexIdIso_hom_app_f, Functor.mapHomologicalComplex_obj_X,
    Functor.id_obj, curriedTensor_obj_obj, id_f, tensorHom_id, id_whiskerRight,
    Iso.app_inv, identityProjectionFormula_inv_app, Functor.id_map, Category.id_comp]
  have h := ι_tensorHom
    ((Functor.mapHomologicalComplexIdIso (ModuleCat ℤ) (.up ℤ)).hom.app K) (𝟙 E) p q n hpq
  simp only [Functor.mapHomologicalComplexIdIso_hom_app_f, Functor.id_obj,
    Functor.mapHomologicalComplex_obj_X, id_f, tensorHom_id,
    id_whiskerRight, Category.id_comp] at h
  refine (Eq.trans ?_ h).symm
  -- Cancel the native identity component without unfolding the tensor degree object.
  exact congrArg (fun f ↦
    ιTensorObj (((𝟭 (ModuleCat ℤ)).mapHomologicalComplex (.up ℤ)).obj K) E p q n hpq ≫ f)
    (Category.id_comp _)

example (K : CochainComplex (ModuleCat ℤ) ℤ) [K.IsKFlat] :
    CochainComplex.IsKFlat (((𝟭 (ModuleCat ℤ)).mapHomologicalComplex (.up ℤ)).obj K) :=
  (𝟭 (ModuleCat ℤ)).isKFlat_mapHomologicalComplex_obj_of_projectionFormula (𝟭 _)
    identityProjectionFormula K

example (X Y : ModuleCat ℤ) (p q : ℤ) :
    let K := (single (ModuleCat ℤ) (.up ℤ) p).obj X
    let E := (single (ModuleCat ℤ) (.up ℤ) q).obj Y
    let t := Functor.mapHomologicalComplexIdIso (ModuleCat ℤ) (.up ℤ)
    ((singleObjXSelf (.up ℤ) p X).inv ⊗ₘ (singleObjXSelf (.up ℤ) q Y).inv) ≫
        (𝟭 (ModuleCat ℤ)).map
          (ιTensorObj (((𝟭 (ModuleCat ℤ)).mapHomologicalComplex (.up ℤ)).obj K) E
            p q (p + q) rfl) ≫
        ((𝟭 (ModuleCat ℤ)).projectionFormulaHomologicalComplexIso (𝟭 _)
          identityProjectionFormula K E).hom.f
          (p + q) ≫
        (tensorHom (𝟙 K) (t.hom.app E)).f (p + q) =
      ((singleObjXSelf (.up ℤ) p X).inv ⊗ₘ (singleObjXSelf (.up ℤ) q Y).inv) ≫
        ιTensorObj K E p q (p + q) rfl := by
  dsimp only
  rw [Functor.map_ι_projectionFormulaHomologicalComplexIso_hom_f_assoc]
  simp [identityProjectionFormula_hom_app]

end TauCeti.Examples.CochainProjectionFormula
