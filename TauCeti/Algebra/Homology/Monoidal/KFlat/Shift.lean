/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.DerivedTensor
public import Mathlib.Algebra.Homology.BifunctorShift

/-!
# Shifts of tensor functors computed by K-flat models

Tensoring with a fixed K-flat complex commutes coherently with integer shifts on the
unbounded derived category. The comparison with total tensor products on complex models
respects these shifts, as do the transformations induced by maps of K-flat models.
Shifting the K-flat model itself also shifts the output, naturally in the derived input.
These are the shift comparisons needed for exactness of derived tensor products.

The comparisons use the signed totalization isomorphisms in Joël Riou's
`Mathlib.Algebra.Homology.BifunctorShift` and Mathlib's localization of functors with
`Functor.CommShift`. In particular the right-variable comparison retains the Koszul sign;
it is not the unsigned reindexing of the summands of the total complex.

## References

* The Stacks Project, More on Algebra, Section 15.60, Tags 06Y2 and 064M.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Functor HomologicalComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasDerivedCategory C]
  [∀ K L : CochainComplex C ℤ, HasTensor K L]

/-- Tensoring with a K-flat model commutes with shifts, with the zero and addition
coherence laws inherited from the signed total tensor product. -/
instance (K : CochainComplex C ℤ) [K.IsKFlat] : K.kFlatTensor.CommShift ℤ :=
  Functor.commShiftOfLocalization DerivedCategory.Q (quasiIso C (.up ℤ)) ℤ
    (((MonoidalCategory.curriedTensor C).map₂CochainComplex.obj K) ⋙ DerivedCategory.Q)
    K.kFlatTensor

/-- The comparison with ordinary tensor products on complex models respects shifts. -/
instance (K : CochainComplex C ℤ) [K.IsKFlat] :
    NatTrans.CommShift K.kFlatTensorModelIso.hom ℤ := by
  rw [kFlatTensorModelIso_eq_liftingIso]
  infer_instance

/-- Maps of K-flat models induce transformations compatible with all integer shifts. -/
instance {K L : CochainComplex C ℤ} [K.IsKFlat] [L.IsKFlat] (f : K ⟶ L) :
    NatTrans.CommShift (kFlatTensorMap f) ℤ := by
  rw [kFlatTensorMap_eq_liftNatTrans]
  exact NatTrans.CommShift.liftNatTrans ..

/-- On a complex model, the shift comparison is the image of the signed totalization
comparison, transported through the localization and model isomorphisms. -/
@[reassoc]
theorem kFlatTensor_commShiftIso_hom_app_Q (K : CochainComplex C ℤ) [K.IsKFlat]
    (A : CochainComplex C ℤ) (n : ℤ) :
    (K.kFlatTensor.commShiftIso n).hom.app (DerivedCategory.Q.obj A) =
      K.kFlatTensor.map ((DerivedCategory.Q.commShiftIso n).inv.app A) ≫
        K.kFlatTensorModelIso.hom.app (A⟦n⟧) ≫
        DerivedCategory.Q.map (mapBifunctorShift₂Iso K A
          (MonoidalCategory.curriedTensor C) n).hom ≫
        (DerivedCategory.Q.commShiftIso n).hom.app (tensorObj K A) ≫
        (CategoryTheory.shiftFunctor (DerivedCategory C) n).map
          (K.kFlatTensorModelIso.inv.app A) := by
  simpa only [kFlatTensorModelIso_eq_liftingIso, Functor.commShiftIso_comp_hom_app,
    Functor.commShiftIso_map₂CochainComplex_hom_app, Functor.comp_obj,
    curriedTensor_map₂CochainComplex_obj_obj, Category.assoc] using
    (Functor.commShiftOfLocalization_iso_hom_app DerivedCategory.Q
      (quasiIso C (.up ℤ))
      (((MonoidalCategory.curriedTensor C).map₂CochainComplex.obj K) ⋙ DerivedCategory.Q)
      K.kFlatTensor n A)

/-- Shifting the K-flat model is naturally equivalent to shifting the output of its
localized tensor functor. The comparison uses the left-variable totalization shift. -/
def kFlatTensorShiftIso (K : CochainComplex C ℤ) [K.IsKFlat] (n : ℤ) :
    (K⟦n⟧).kFlatTensor ≅
      K.kFlatTensor ⋙ CategoryTheory.shiftFunctor (DerivedCategory C) n :=
  Localization.liftNatIso DerivedCategory.Q (quasiIso C (.up ℤ))
    (((MonoidalCategory.curriedTensor C).map₂CochainComplex.obj (K⟦n⟧)) ⋙ DerivedCategory.Q)
    ((((MonoidalCategory.curriedTensor C).map₂CochainComplex.obj K) ⋙ DerivedCategory.Q) ⋙
      CategoryTheory.shiftFunctor (DerivedCategory C) n) _ _
    (isoWhiskerRight
      (NatIso.ofComponents (fun A ↦ mapBifunctorShift₁Iso K A
        (MonoidalCategory.curriedTensor C) n) (fun f ↦
          (NatTrans.shift_app_comm
            ((MonoidalCategory.curriedTensor C).map₂CochainComplex.flip.map f) n K).symm))
        DerivedCategory.Q ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft ((MonoidalCategory.curriedTensor C).map₂CochainComplex.obj K)
        (DerivedCategory.Q.commShiftIso n) ≪≫ (Functor.associator _ _ _).symm)

/-- The shifted-model comparison is computed by the left-variable totalization shift,
conjugated by the model comparisons. -/
@[reassoc]
theorem kFlatTensorShiftIso_hom_app_Q (K : CochainComplex C ℤ) [K.IsKFlat]
    (A : CochainComplex C ℤ) (n : ℤ) :
    (K.kFlatTensorShiftIso n).hom.app (DerivedCategory.Q.obj A) =
      (K⟦n⟧).kFlatTensorModelIso.hom.app A ≫
        DerivedCategory.Q.map (mapBifunctorShift₁Iso K A
          (MonoidalCategory.curriedTensor C) n).hom ≫
        (DerivedCategory.Q.commShiftIso n).hom.app (tensorObj K A) ≫
        (CategoryTheory.shiftFunctor (DerivedCategory C) n).map
          (K.kFlatTensorModelIso.inv.app A) := by
  simp [kFlatTensorShiftIso, kFlatTensorModelIso_eq_liftingIso, Localization.Lifting.compRight_iso,
    NatIso.ofComponents]

end CochainComplex
