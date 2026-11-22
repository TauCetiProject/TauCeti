/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Tensoring cochain complexes with the monoidal unit

The right unitors identify the degreewise tensor product `K ⊗ 𝟙` with `K`.
The left unitor identifies `𝟙[0] ⊗ T` with `T[0]`, naturally in `T`.
These identifications allow computations with tensor units independently of internal Hom.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CochainComplex.HomComplex

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C]

/-- The isomorphism of complexes `K ⊗ 𝟙 ≅ K` given by the right unitors
(`MonoidalCategory.rightUnitorNatIso` applied degreewise). -/
def tensorRightUnitIso (K : CochainComplex C ℤ) :
    ((tensorRight (𝟙_ C)).mapHomologicalComplex _).obj K ≅ K :=
  (NatIso.mapHomologicalComplex (rightUnitorNatIso C) _).app K ≪≫
    (Functor.mapHomologicalComplexIdIso C _).app K

@[simp]
lemma tensorRightUnitIso_hom_f (K : CochainComplex C ℤ) (p : ℤ) :
    (tensorRightUnitIso K).hom.f p = (ρ_ (K.X p)).hom := by
  simp [tensorRightUnitIso]

@[simp]
lemma tensorRightUnitIso_inv_f (K : CochainComplex C ℤ) (p : ℤ) :
    (tensorRightUnitIso K).inv.f p = (ρ_ (K.X p)).inv := by
  simp [tensorRightUnitIso]

variable [HasZeroObject C]

/-- The isomorphism of complexes `𝟙[0] ⊗ T ≅ T[0]` given by the left unitor. -/
def singleUnitTensorIso (T : C) :
    ((tensorRight T).mapHomologicalComplex _).obj ((singleFunctor C 0).obj (𝟙_ C)) ≅
      (singleFunctor C 0).obj T :=
  (HomologicalComplex.singleMapHomologicalComplex (tensorRight T) _ 0).app (𝟙_ C) ≪≫
    (singleFunctor C 0).mapIso (λ_ T)

/-- In degree zero the inverse of `𝟙[0] ⊗ T ≅ T[0]` is the inverse left unitor,
under the canonical identifications with the degree zero terms of single complexes. -/
@[simp]
lemma singleUnitTensorIso_inv_f_zero (T : C) :
    (singleUnitTensorIso T).inv.f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 T).hom ≫ (λ_ T).inv ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ C)).inv ▷ T := by
  simp only [singleUnitTensorIso, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
    HomologicalComplex.comp_f, HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    singleFunctor, HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc,
    Functor.flip_obj_map, curriedTensor_map_app]

/-- The inverse of `𝟙[0] ⊗ T ≅ T[0]` is natural in `T`, expressed as degree zero cochains. -/
lemma singleUnitTensorIso_inv_naturality {T' T : C} (g : T' ⟶ T) :
    (Cochain.ofHom (singleUnitTensorIso T').inv).comp
        (Cochain.ofHom ((NatTrans.mapHomologicalComplex ((curriedTensor C).flip.map g) _).app _))
        (zero_add 0) =
      (Cochain.ofHom ((singleFunctor C 0).map g)).comp
        (Cochain.ofHom (singleUnitTensorIso T).inv) (zero_add 0) := by
  rw [← Cochain.ofHom_comp, ← Cochain.ofHom_comp]
  refine congrArg Cochain.ofHom (HomologicalComplex.hom_ext _ _ fun p ↦ ?_)
  by_cases hp : p = 0
  · subst hp
    simp only [singleUnitTensorIso, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
      HomologicalComplex.comp_f, HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      HomologicalComplex.single_map_f_self, Category.assoc,
      Iso.inv_hom_id_assoc, Functor.flip_obj_map, curriedTensor_map_app, singleFunctor,
      NatTrans.mapHomologicalComplex_app_f, Functor.flip_map_app, curriedTensor_obj_map]
    rw [← whisker_exchange, leftUnitor_inv_naturality_assoc, leftUnitor_inv_naturality_assoc,
      leftUnitor_inv_naturality_assoc]
  · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_src _ _

end CochainComplex
