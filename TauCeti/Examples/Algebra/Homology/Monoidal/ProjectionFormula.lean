/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.ProjectionFormula
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits

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

/-- The ordinary projection formula for the identity functors on abelian groups. -/
def identityProjection :
    (𝟭 (ModuleCat ℤ)).prod (𝟭 (ModuleCat ℤ)) ⋙ tensor (ModuleCat ℤ) ⋙ 𝟭 (ModuleCat ℤ) ≅
      (𝟭 (ModuleCat ℤ)).prod (𝟭 (ModuleCat ℤ)) ⋙ tensor (ModuleCat ℤ) :=
  Functor.isoWhiskerLeft _ (Functor.rightUnitor _)

private lemma identityProjection_hom (K E : CochainComplex (ModuleCat ℤ) ℤ) :
    let t := Functor.mapHomologicalComplexIdIso (ModuleCat ℤ) (.up ℤ)
    ((𝟭 (ModuleCat ℤ)).projectionFormulaCochainIso (𝟭 _) identityProjection K E).hom ≫
        tensorHom (𝟙 K) (t.hom.app E) =
      t.hom.app _ ≫ tensorHom (t.hom.app K) (𝟙 E) := by
  dsimp only
  apply (cancel_epi
    ((𝟭 (ModuleCat ℤ)).projectionFormulaCochainIso (𝟭 _) identityProjection K E).inv).1
  apply Hom.ext
  funext n
  refine mapBifunctor.hom_ext fun p q hpq ↦ ?_
  simp only [Functor.mapHomologicalComplex_obj_X, Functor.id_obj, curriedTensor_obj_obj,
    Iso.inv_hom_id_assoc, ι_mapBifunctorMap, id_f,
    Functor.mapHomologicalComplexIdIso_hom_app_f, curriedTensor_obj_map, whiskerLeft_id,
    Category.id_comp, Functor.mapBifunctorHomologicalComplex_obj_obj_toGradedObject, comp_f,
    Functor.ι_projectionFormulaCochainIso_inv_f_assoc, Functor.prod_obj, tensor_obj,
    Iso.app_inv, Functor.id_map]
  -- Evaluate the native identity comparison on the totalization summand.
  erw [Category.id_comp, ι_tensorHom]
  simp

example (K : CochainComplex (ModuleCat ℤ) ℤ) [K.IsKFlat] :
    CochainComplex.IsKFlat (((𝟭 (ModuleCat ℤ)).mapHomologicalComplex (.up ℤ)).obj K) :=
  (𝟭 (ModuleCat ℤ)).isKFlat_mapHomologicalComplex_obj_of_projectionFormula (𝟭 _)
    identityProjection (Functor.rightUnitor _) K

example (X Y : ModuleCat ℤ) (p q : ℤ) :
    let K := (single (ModuleCat ℤ) (.up ℤ) p).obj X
    let E := (single (ModuleCat ℤ) (.up ℤ) q).obj Y
    let t := Functor.mapHomologicalComplexIdIso (ModuleCat ℤ) (.up ℤ)
    ((singleObjXSelf (.up ℤ) p X).inv ⊗ₘ (singleObjXSelf (.up ℤ) q Y).inv) ≫
        (𝟭 (ModuleCat ℤ)).map
          (ιTensorObj (((𝟭 (ModuleCat ℤ)).mapHomologicalComplex (.up ℤ)).obj K) E
            p q (p + q) rfl) ≫
        ((𝟭 (ModuleCat ℤ)).projectionFormulaCochainIso (𝟭 _) identityProjection K E).hom.f
          (p + q) ≫
        (tensorHom (𝟙 K) (t.hom.app E)).f (p + q) =
      ((singleObjXSelf (.up ℤ) p X).inv ⊗ₘ (singleObjXSelf (.up ℤ) q Y).inv) ≫
        ιTensorObj K E p q (p + q) rfl := by
  dsimp only
  rw [Functor.map_ι_projectionFormulaCochainIso_hom_f_assoc]
  simp [identityProjection]

end TauCeti.Examples.CochainProjectionFormula
