/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.KFlat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Tensoring derived objects with a K-flat complex

Tensoring with a fixed K-flat complex preserves quasi-isomorphisms, hence descends to an
endofunctor of the unbounded derived category. `CochainComplex.kFlatTensor` is this functor;
`CochainComplex.kFlatTensorModelIso` identifies its value on a complex with the usual
direct-sum total tensor product. Maps between K-flat complexes induce natural transformations,
with identity and composition laws and a formula on complex models.

Only the fixed left factor is required to be K-flat. No boundedness or termwise flatness
is required of the right factor. This is the model computation used to construct derived
tensor products, not a choice of a K-flat replacement for every derived object.

## References

* The Stacks Project, More on Algebra, Section 15.60, Tags 064L and 064M.

The descent uses Mathlib's `Localization.lift` and `Localization.liftNatTrans`.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Functor HomologicalComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasDerivedCategory C]
  [∀ K L : CochainComplex C ℤ, HasTensor K L]

/-- Tensoring with a K-flat complex, followed by localization, inverts quasi-isomorphisms. -/
theorem isInvertedBy_tensor_comp_Q (K : CochainComplex C ℤ) [K.IsKFlat] :
    (quasiIso C (.up ℤ)).IsInvertedBy
      (((CategoryTheory.MonoidalCategory.curriedTensor C).map₂CochainComplex.obj K) ⋙
        DerivedCategory.Q) := by
  intro A B f hf
  have : QuasiIso f := hf
  simpa only [Functor.comp_map, Functor.comp_obj, curriedTensor_map₂CochainComplex_obj_obj,
    curriedTensor_map₂CochainComplex_obj_map] using
    (inferInstance : IsIso (DerivedCategory.Q.map (tensorHom (𝟙 K) f)))

/-- Tensoring a derived object with the specified K-flat complex on the left. -/
def kFlatTensor (K : CochainComplex C ℤ) [K.IsKFlat] :
    DerivedCategory C ⥤ DerivedCategory C :=
  Localization.lift
    (((CategoryTheory.MonoidalCategory.curriedTensor C).map₂CochainComplex.obj K) ⋙
      DerivedCategory.Q)
    K.isInvertedBy_tensor_comp_Q DerivedCategory.Q

/-- The derived tensor functor is the localization lift of the ordinary total tensor. -/
theorem kFlatTensor_eq_lift (K : CochainComplex C ℤ) [K.IsKFlat] :
    K.kFlatTensor = Localization.lift
      (((CategoryTheory.MonoidalCategory.curriedTensor C).map₂CochainComplex.obj K) ⋙
        DerivedCategory.Q) K.isInvertedBy_tensor_comp_Q DerivedCategory.Q := (rfl)

instance (K : CochainComplex C ℤ) [K.IsKFlat] :
    Localization.Lifting DerivedCategory.Q (quasiIso C (.up ℤ))
      (((CategoryTheory.MonoidalCategory.curriedTensor C).map₂CochainComplex.obj K) ⋙
        DerivedCategory.Q) K.kFlatTensor := by
  rw [kFlatTensor_eq_lift]
  infer_instance

/-- The tensor with a K-flat complex is computed by the ordinary total tensor on complex models.
This comparison is natural in the right factor. -/
def kFlatTensorModelIso (K : CochainComplex C ℤ) [K.IsKFlat] :
    DerivedCategory.Q ⋙ K.kFlatTensor ≅
      ((CategoryTheory.MonoidalCategory.curriedTensor C).map₂CochainComplex.obj K) ⋙
        DerivedCategory.Q :=
  Localization.Lifting.iso _ (quasiIso C (.up ℤ)) _ _

/-- The model comparison is the canonical factorization isomorphism of the localization. -/
theorem kFlatTensorModelIso_eq_liftingIso (K : CochainComplex C ℤ) [K.IsKFlat] :
    K.kFlatTensorModelIso = Localization.Lifting.iso DerivedCategory.Q (quasiIso C (.up ℤ))
      (((CategoryTheory.MonoidalCategory.curriedTensor C).map₂CochainComplex.obj K) ⋙
        DerivedCategory.Q) K.kFlatTensor := (rfl)

/-- A map between K-flat complexes induces a transformation of their derived tensor functors. -/
def kFlatTensorMap {K L : CochainComplex C ℤ} [K.IsKFlat] [L.IsKFlat] (f : K ⟶ L) :
    K.kFlatTensor ⟶ L.kFlatTensor :=
  Localization.liftNatTrans DerivedCategory.Q (quasiIso C (.up ℤ)) _ _ _ _
    (whiskerRight ((CategoryTheory.MonoidalCategory.curriedTensor C).map₂CochainComplex.map f)
      DerivedCategory.Q)

/-- The induced transformation is the localization lift of the ordinary tensor transformation. -/
theorem kFlatTensorMap_eq_liftNatTrans {K L : CochainComplex C ℤ}
    [K.IsKFlat] [L.IsKFlat] (f : K ⟶ L) :
    kFlatTensorMap f = Localization.liftNatTrans DerivedCategory.Q (quasiIso C (.up ℤ))
      _ _ K.kFlatTensor L.kFlatTensor
      (whiskerRight ((CategoryTheory.MonoidalCategory.curriedTensor C).map₂CochainComplex.map f)
        DerivedCategory.Q) := by
  rfl

/-- On a complex model, the transformation is the image of tensoring the given map with the
identity, conjugated by the model comparisons. -/
theorem kFlatTensorMap_app_Q {K L : CochainComplex C ℤ} [K.IsKFlat] [L.IsKFlat]
    (f : K ⟶ L) (A : CochainComplex C ℤ) :
    (kFlatTensorMap f).app (DerivedCategory.Q.obj A) =
      (K.kFlatTensorModelIso.app A).hom ≫ DerivedCategory.Q.map (tensorHom f (𝟙 A)) ≫
        (L.kFlatTensorModelIso.app A).inv := by
  simp only [kFlatTensorMap, Localization.liftNatTrans_app, whiskerRight_app,
    curriedTensor_map₂CochainComplex_map_app, kFlatTensorModelIso, Iso.app_hom, Iso.app_inv,
    Functor.comp_obj, curriedTensor_map₂CochainComplex_obj_obj]

/-- The model comparison intertwines the induced transformation with the ordinary tensor map. -/
@[reassoc (attr := simp)]
theorem kFlatTensorMap_app_Q_comp {K L : CochainComplex C ℤ} [K.IsKFlat] [L.IsKFlat]
    (f : K ⟶ L) (A : CochainComplex C ℤ) :
    (kFlatTensorMap f).app (DerivedCategory.Q.obj A) ≫ L.kFlatTensorModelIso.hom.app A =
      K.kFlatTensorModelIso.hom.app A ≫ DerivedCategory.Q.map (tensorHom f (𝟙 A)) := by
  rw [← Iso.app_hom K.kFlatTensorModelIso A, ← Iso.app_hom L.kFlatTensorModelIso A,
    kFlatTensorMap_app_Q]
  simp only [Category.assoc, ← curriedTensor_map₂CochainComplex_obj_obj L A,
    Iso.inv_hom_id, Category.comp_id]

@[simp]
theorem kFlatTensorMap_id (K : CochainComplex C ℤ) [K.IsKFlat] :
    kFlatTensorMap (𝟙 K) = 𝟙 K.kFlatTensor := by
  simp [kFlatTensorMap]

@[simp]
theorem kFlatTensorMap_comp {K L M : CochainComplex C ℤ}
    [K.IsKFlat] [L.IsKFlat] [M.IsKFlat] (f : K ⟶ L) (g : L ⟶ M) :
    kFlatTensorMap (f ≫ g) = kFlatTensorMap f ≫ kFlatTensorMap g := by
  simp only [kFlatTensorMap, Functor.map_comp, whiskerRight_comp]
  exact (Localization.comp_liftNatTrans DerivedCategory.Q (quasiIso C (.up ℤ))
    _ _ _ _ _ _ _ _).symm

end CochainComplex
