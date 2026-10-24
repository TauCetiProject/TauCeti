/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Single
public import TauCeti.Algebra.Homology.Bifunctor.Support

/-!
# The left unitor of a bifunctor on complexes

Let `F : C ⥤ D ⥤ D` be a bifunctor and `X` an object of `C` with `e : F.obj X ≅ 𝟭 D`. Then the
complex `X[0]` acts as the identity through the totalized bifunctor: for every complex shape `c`
with tensor signs (`ComplexShape.TensorSigns`) and every complex `K`, there is an isomorphism
`mapBifunctor X[0] K F c ≅ K`, natural in `K`.

## Main definitions

* `CategoryTheory.Functor.mapBifunctorLeftUnitor`: the isomorphism `mapBifunctor X[0] K F c ≅ K`
  attached to `e : F.obj X ≅ 𝟭 D`.

This adapts Mathlib's `CategoryTheory.GradedObject.mapBifunctorLeftUnitor` and the left unitor
`HomologicalComplex.leftUnitor` of the monoidal structure on homological complexes, both due to
Joël Riou, from tensor products to arbitrary bifunctors on complexes.
-/

public section

noncomputable section

open CategoryTheory Category Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroMorphisms C] [HasZeroObject C] [Preadditive D]
  (F : C ⥤ D ⥤ D) [F.PreservesZeroMorphisms] [∀ X, (F.obj X).PreservesZeroMorphisms]
  (X : C) (e : F.obj X ≅ 𝟭 D)
  {I : Type*} [AddMonoid I] [DecidableEq I] {c : ComplexShape I} [c.TensorSigns]

open HomologicalComplex

/-- The term of degree `j` of `mapBifunctor X[0] K F c` is `K.X j`, given `e : F.obj X ≅ 𝟭 D`. -/
private def mapBifunctorLeftUnitorX (K : HomologicalComplex D c)
    [HasMapBifunctor ((single C c 0).obj X) K F c] (j : I) :
    (mapBifunctor ((single C c 0).obj X) K F c).X j ≅ K.X j :=
  mapBifunctorSingleSummandIso _ K F c 0 j j (zero_add j) (fun p q hpq hne ↦ by
      have hp : p ≠ 0 := by
        rintro rfl
        exact hne ⟨rfl, by simpa using hpq⟩
      exact (F.flip.obj (K.X q)).map_isZero (isZero_single_obj_X c 0 X p hp)) ≪≫
    (F.mapIso (singleObjXSelf c 0 X)).app (K.X j) ≪≫ e.app (K.X j)

private lemma mapBifunctorLeftUnitorX_inv (K : HomologicalComplex D c)
    [HasMapBifunctor ((single C c 0).obj X) K F c] (j : I) :
    (mapBifunctorLeftUnitorX F X e K j).inv =
      e.inv.app (K.X j) ≫ (F.map (singleObjXSelf c 0 X).inv).app (K.X j) ≫
        ιMapBifunctor _ K F c 0 j j (zero_add j) := by
  simp [mapBifunctorLeftUnitorX]

private lemma mapBifunctorLeftUnitorX_inv_comm (K : HomologicalComplex D c)
    [HasMapBifunctor ((single C c 0).obj X) K F c] (j j' : I) :
    (mapBifunctorLeftUnitorX F X e K j).inv ≫
        (mapBifunctor ((single C c 0).obj X) K F c).d j j' =
      K.d j j' ≫ (mapBifunctorLeftUnitorX F X e K j').inv := by
  by_cases hjj' : c.Rel j j'
  · -- The first-variable differential vanishes since `X[0]` has zero differential.
    have hd₁ : mapBifunctor.d₁ ((single C c 0).obj X) K F c 0 j j' = 0 := by
      by_cases h₁ : c.Rel 0 (c.next 0)
      · by_cases h₂ : ComplexShape.π c c c (c.next 0, j) = j'
        · rw [mapBifunctor.d₁_eq _ _ _ _ h₁ _ _ h₂, single_obj_d, Functor.map_zero,
            NatTrans.app_zero, zero_comp, smul_zero]
        · rw [mapBifunctor.d₁_eq_zero' _ _ _ _ h₁ _ _ h₂]
      · rw [mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ h₁]
    have hε : ComplexShape.ε₂ c c c (0, j) = 1 := by simp
    rw [mapBifunctorLeftUnitorX_inv, mapBifunctorLeftUnitorX_inv]
    simp only [assoc, mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁,
      mapBifunctor.ι_D₂, hd₁, comp_zero, zero_add,
      mapBifunctor.d₂_eq _ _ _ _ _ hjj' _ (by simp : ComplexShape.π c c c (0, j') = j'), hε,
      one_smul]
    rw [← NatTrans.naturality_assoc, ← e.inv.naturality_assoc, Functor.id_map]
  · simp only [shape _ _ _ hjj', comp_zero, zero_comp]

/-- The left unitor `mapBifunctor X[0] K F c ≅ K` attached to an isomorphism
`e : F.obj X ≅ 𝟭 D`. -/
def mapBifunctorLeftUnitor (K : HomologicalComplex D c)
    [HasMapBifunctor ((single C c 0).obj X) K F c] :
    mapBifunctor ((single C c 0).obj X) K F c ≅ K :=
  (Hom.isoOfComponents (fun j ↦ (mapBifunctorLeftUnitorX F X e K j).symm)
    (fun j j' _ ↦ mapBifunctorLeftUnitorX_inv_comm F X e K j j')).symm

@[reassoc (attr := simp)]
lemma ι_mapBifunctorLeftUnitor_hom_f (K : HomologicalComplex D c)
    [HasMapBifunctor ((single C c 0).obj X) K F c] (j : I) :
    ιMapBifunctor _ K F c 0 j j (zero_add j) ≫ (mapBifunctorLeftUnitor F X e K).hom.f j =
      (F.map (singleObjXSelf c 0 X).hom).app (K.X j) ≫ e.hom.app (K.X j) := by
  simp [mapBifunctorLeftUnitor, mapBifunctorLeftUnitorX]

@[simp, reassoc]
lemma mapBifunctorLeftUnitor_inv_f (K : HomologicalComplex D c)
    [HasMapBifunctor ((single C c 0).obj X) K F c] (j : I) :
    (mapBifunctorLeftUnitor F X e K).inv.f j =
      e.inv.app (K.X j) ≫ (F.map (singleObjXSelf c 0 X).inv).app (K.X j) ≫
        ιMapBifunctor _ K F c 0 j j (zero_add j) :=
  mapBifunctorLeftUnitorX_inv F X e K j

@[reassoc]
lemma mapBifunctorLeftUnitor_inv_naturality {K L : HomologicalComplex D c} (f : K ⟶ L)
    [HasMapBifunctor ((single C c 0).obj X) K F c]
    [HasMapBifunctor ((single C c 0).obj X) L F c] :
    f ≫ (mapBifunctorLeftUnitor F X e L).inv =
      (mapBifunctorLeftUnitor F X e K).inv ≫ mapBifunctorMap (𝟙 _) f F c := by
  ext j
  have h := (F.map (singleObjXSelf c 0 X).inv).naturality (f.f j)
  have h' := e.inv.naturality (f.f j)
  dsimp at h h'
  simp [reassoc_of% h, reassoc_of% h']

@[reassoc]
lemma mapBifunctorLeftUnitor_naturality {K L : HomologicalComplex D c} (f : K ⟶ L)
    [HasMapBifunctor ((single C c 0).obj X) K F c]
    [HasMapBifunctor ((single C c 0).obj X) L F c] :
    mapBifunctorMap (𝟙 _) f F c ≫ (mapBifunctorLeftUnitor F X e L).hom =
      (mapBifunctorLeftUnitor F X e K).hom ≫ f := by
  rw [← cancel_mono (mapBifunctorLeftUnitor F X e L).inv, assoc, assoc, Iso.hom_inv_id,
    comp_id, mapBifunctorLeftUnitor_inv_naturality, Iso.hom_inv_id_assoc]

end CategoryTheory.Functor
