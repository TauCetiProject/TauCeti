/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.BifunctorHomotopy

/-!
# Bifunctors on homological complexes preserve homotopy equivalences

Let `F : C₁ ⥤ C₂ ⥤ D` be a bifunctor which is additive in each variable, and let
`mapBifunctor K₁ K₂ F c` be the induced total complex of homological complexes `K₁` and `K₂`
(for `F` the tensor product this is the tensor product of complexes).  Mathlib's
`HomologicalComplex.mapBifunctorMapHomotopy₁` and `HomologicalComplex.mapBifunctorMapHomotopy₂`
show that `mapBifunctorMap f₁ f₂ F c` only depends on the homotopy classes of `f₁` and `f₂`.
This file records that `mapBifunctorMap` is functorial in the pair `(f₁, f₂)`, and deduces that
homotopy equivalences `K₁ ≃ L₁` and `K₂ ≃ L₂` induce a homotopy equivalence
`mapBifunctor K₁ K₂ F c ≃ mapBifunctor L₁ L₂ F c`.  In particular the homology of a tensor
product of complexes only depends on the homotopy types of the factors, which is how the Künneth
theorem reduces to complexes with zero differential.

## Main definitions and results

* `HomologicalComplex.mapBifunctorMap_id` and `HomologicalComplex.mapBifunctorMap_comp`:
  functoriality of `mapBifunctorMap` in both variables simultaneously.
* `HomotopyEquiv.mapBifunctor`: the homotopy equivalence of total complexes induced by
  homotopy equivalences of the two factors.
-/

public section

noncomputable section

open CategoryTheory Limits

variable {C₁ C₂ D I₁ I₂ J : Type*} [Category* C₁] [Category* C₂] [Category* D]
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}

namespace HomologicalComplex

variable [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms] [∀ X₁, (F.obj X₁).PreservesZeroMorphisms]
  (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]

/-- `mapBifunctorMap` sends the pair of identities to the identity. -/
@[simp]
lemma mapBifunctorMap_id (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂)
    [HasMapBifunctor K₁ K₂ F c] :
    mapBifunctorMap (𝟙 K₁) (𝟙 K₂) F c = 𝟙 _ := by
  ext
  simp

/-- `mapBifunctorMap` is compatible with composition in both variables simultaneously. -/
@[reassoc]
lemma mapBifunctorMap_comp {K₁ L₁ M₁ : HomologicalComplex C₁ c₁}
    {K₂ L₂ M₂ : HomologicalComplex C₂ c₂} [HasMapBifunctor K₁ K₂ F c]
    [HasMapBifunctor L₁ L₂ F c] [HasMapBifunctor M₁ M₂ F c]
    (f₁ : K₁ ⟶ L₁) (g₁ : L₁ ⟶ M₁) (f₂ : K₂ ⟶ L₂) (g₂ : L₂ ⟶ M₂) :
    mapBifunctorMap (f₁ ≫ g₁) (f₂ ≫ g₂) F c =
      mapBifunctorMap f₁ f₂ F c ≫ mapBifunctorMap g₁ g₂ F c := by
  ext
  simp [NatTrans.naturality_assoc]

end HomologicalComplex

namespace HomotopyEquiv

open HomologicalComplex

variable [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  {F : C₁ ⥤ C₂ ⥤ D} [F.Additive] [∀ X₁, (F.obj X₁).Additive]
  {c : ComplexShape J} [DecidableEq J] [TotalComplexShape c₁ c₂ c]
  {K₁ L₁ : HomologicalComplex C₁ c₁} {K₂ L₂ : HomologicalComplex C₂ c₂}
  [HasMapBifunctor K₁ K₂ F c] [HasMapBifunctor L₁ L₂ F c]

/-- A homotopy between `f₁ ≫ g₁` and `𝟙` and a homotopy between `f₂ ≫ g₂` and `𝟙` induce a
homotopy between `mapBifunctorMap f₁ f₂ F c ≫ mapBifunctorMap g₁ g₂ F c` and `𝟙`. -/
private def mapBifunctorHomotopyId (f₁ : K₁ ⟶ L₁) (g₁ : L₁ ⟶ K₁) (f₂ : K₂ ⟶ L₂)
    (g₂ : L₂ ⟶ K₂) (h₁ : Homotopy (f₁ ≫ g₁) (𝟙 K₁)) (h₂ : Homotopy (f₂ ≫ g₂) (𝟙 K₂)) :
    Homotopy (mapBifunctorMap f₁ f₂ F c ≫ mapBifunctorMap g₁ g₂ F c) (𝟙 _) :=
  (Homotopy.ofEq (mapBifunctorMap_comp F c f₁ g₁ f₂ g₂).symm).trans
    (((mapBifunctorMapHomotopy₁ h₁ (f₂ ≫ g₂) F c).trans
      (mapBifunctorMapHomotopy₂ (𝟙 K₁) h₂ F c)).trans
        (Homotopy.ofEq (mapBifunctorMap_id F c K₁ K₂)))

variable (F c) in
/-- Homotopy equivalences `K₁ ≃ L₁` and `K₂ ≃ L₂` induce a homotopy equivalence
`mapBifunctor K₁ K₂ F c ≃ mapBifunctor L₁ L₂ F c`, given by `mapBifunctorMap` of the two
homotopy equivalences and of their inverses. -/
def mapBifunctor (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂) :
    HomotopyEquiv (HomologicalComplex.mapBifunctor K₁ K₂ F c)
      (HomologicalComplex.mapBifunctor L₁ L₂ F c) where
  hom := mapBifunctorMap e₁.hom e₂.hom F c
  inv := mapBifunctorMap e₁.inv e₂.inv F c
  homotopyHomInvId :=
    mapBifunctorHomotopyId _ _ _ _ e₁.homotopyHomInvId e₂.homotopyHomInvId
  homotopyInvHomId :=
    mapBifunctorHomotopyId _ _ _ _ e₁.homotopyInvHomId e₂.homotopyInvHomId

/-- The forward map of `HomotopyEquiv.mapBifunctor`. -/
@[simp]
lemma mapBifunctor_hom (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂) :
    (mapBifunctor F c e₁ e₂).hom = mapBifunctorMap e₁.hom e₂.hom F c :=
  (rfl)

/-- The backward map of `HomotopyEquiv.mapBifunctor`. -/
@[simp]
lemma mapBifunctor_inv (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂) :
    (mapBifunctor F c e₁ e₂).inv = mapBifunctorMap e₁.inv e₂.inv F c :=
  (rfl)

end HomotopyEquiv
