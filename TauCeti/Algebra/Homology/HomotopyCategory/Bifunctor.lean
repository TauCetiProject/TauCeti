/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.Single
public import TauCeti.Algebra.Homology.Bifunctor.Associator
public import TauCeti.Algebra.Homology.Bifunctor.Homotopy
public import TauCeti.Algebra.Homology.Bifunctor.Support

/-!
# Bifunctors on homotopy categories

Let `F : C₁ ⥤ C₂ ⥤ D` be a bifunctor which is additive in each variable. Mathlib's
`CategoryTheory.Functor.map₂HomologicalComplex` sends complexes `K₁` and `K₂` to the total
complex `mapBifunctor K₁ K₂ F c`, and `HomologicalComplex.mapBifunctorMapHomotopy₁` and
`HomologicalComplex.mapBifunctorMapHomotopy₂` show that `mapBifunctorMap f₁ f₂ F c` only depends
on the homotopy classes of `f₁` and `f₂`. Hence the totalized bifunctor descends to a bifunctor

```text
F.map₂HomotopyCategory c₁ c₂ c : K(C₁) ⥤ K(C₂) ⥤ K(D)
```

on homotopy categories, which agrees with the totalized bifunctor on the images of complexes.
In particular a homotopy equivalence in either variable becomes an isomorphism.

If `F.obj X ≅ 𝟭 D` for an object `X` of `C₁`, then the complex `X[0]` acts as the identity:
`mapBifunctor X[0] K F c ≅ K`, naturally in `K`. This holds already for complexes, for every
complex shape `c` with tensor signs (`ComplexShape.TensorSigns`), and descends to an isomorphism
between the functor of the homotopy category given by `X[0]` and the identity functor.

Similarly, an associator between two composite trifunctors induces, through Mathlib's
`HomologicalComplex.mapBifunctorAssociator`, an isomorphism between acting by a total complex
`mapBifunctor K₁ K₂ F₁₂ c₁₂` and acting by `K₂` and then by `K₁`.

These constructions turn a complex of bimodules into an endofunctor of the homotopy category of
modules: this is how complexes of bimodules, such as the braid complexes of a zigzag algebra, act
on homotopy categories.

## Main definitions

* `CategoryTheory.Functor.map₂HomotopyCategory`: the bifunctor on homotopy categories induced by
  a bifunctor `F`.
* `CategoryTheory.Functor.mapBifunctorLeftUnitor`: the isomorphism `mapBifunctor X[0] K F c ≅ K`
  attached to `e : F.obj X ≅ 𝟭 D`.
* `CategoryTheory.Functor.map₂HomotopyCategoryLeftUnitor`: its descent, an isomorphism between
  `(F.map₂HomotopyCategory c c c).obj X[0]` and the identity functor of `K(D)`.
* `CategoryTheory.Functor.map₂HomotopyCategoryAssociator`: the descent of the totalized
  associator to homotopy categories.

The left unitor adapts Mathlib's `CategoryTheory.GradedObject.mapBifunctorLeftUnitor` and the
left unitor `HomologicalComplex.leftUnitor` of the monoidal structure on homological complexes,
both due to Joël Riou, from tensor products to arbitrary bifunctors on complexes.
-/

public section

noncomputable section

open CategoryTheory Category Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X₁, (F.obj X₁).Additive]
  {I₁ I₂ J : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂) (c : ComplexShape J)
  [DecidableEq J] [TotalComplexShape c₁ c₂ c]
  [∀ (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F c]

open HomologicalComplex

/-- The bifunctor on homotopy categories induced by a bifunctor `F` which is additive in each
variable. On the images of complexes `K₁` and `K₂` it is the total complex
`mapBifunctor K₁ K₂ F c`. -/
-- Expose the object assignment so that actions on images of complexes have computed types.
@[expose]
def map₂HomotopyCategory :
    HomotopyCategory C₁ c₁ ⥤ HomotopyCategory C₂ c₂ ⥤ HomotopyCategory D c :=
  CategoryTheory.Quotient.lift _
    { obj K₁ := CategoryTheory.Quotient.lift _
        ((F.map₂HomologicalComplex c₁ c₂ c).obj K₁ ⋙ HomotopyCategory.quotient D c)
        (fun _ _ _ _ ⟨h⟩ ↦ HomotopyCategory.eq_of_homotopy _ _
          (mapBifunctorMapHomotopy₂ (𝟙 K₁) h F c))
      map f := CategoryTheory.Quotient.natTransLift _
        (Functor.whiskerRight ((F.map₂HomologicalComplex c₁ c₂ c).map f)
          (HomotopyCategory.quotient D c))
      -- After `simp`, both sides agree up to `Quotient.lift_obj_functor_obj`, which is `rfl`.
      map_id K₁ := by
        apply CategoryTheory.Quotient.natTrans_ext
        ext K₂
        simp only [Functor.map_id, Functor.whiskerLeft_app]
        rfl
      map_comp f g := by
        apply CategoryTheory.Quotient.natTrans_ext
        ext K₂
        simp only [Functor.map_comp, Functor.whiskerLeft_app]
        rfl }
    (fun _ _ _ _ ⟨h⟩ ↦ by
      apply CategoryTheory.Quotient.natTrans_ext
      ext K₂
      exact HomotopyCategory.eq_of_homotopy _ _ (mapBifunctorMapHomotopy₁ h (𝟙 K₂) F c))

@[simp]
lemma map₂HomotopyCategory_obj_obj (K₁ : HomologicalComplex C₁ c₁)
    (K₂ : HomologicalComplex C₂ c₂) :
    ((F.map₂HomotopyCategory c₁ c₂ c).obj ((HomotopyCategory.quotient C₁ c₁).obj K₁)).obj
        ((HomotopyCategory.quotient C₂ c₂).obj K₂) =
      (HomotopyCategory.quotient D c).obj (mapBifunctor K₁ K₂ F c) :=
  (rfl)

@[simp]
lemma map₂HomotopyCategory_obj_map (K₁ : HomologicalComplex C₁ c₁)
    {K₂ L₂ : HomologicalComplex C₂ c₂} (f₂ : K₂ ⟶ L₂) :
    ((F.map₂HomotopyCategory c₁ c₂ c).obj ((HomotopyCategory.quotient C₁ c₁).obj K₁)).map
        ((HomotopyCategory.quotient C₂ c₂).map f₂) =
      (HomotopyCategory.quotient D c).map (mapBifunctorMap (𝟙 K₁) f₂ F c) :=
  (rfl)

@[simp]
lemma map₂HomotopyCategory_map_app {K₁ L₁ : HomologicalComplex C₁ c₁} (f₁ : K₁ ⟶ L₁)
    (K₂ : HomologicalComplex C₂ c₂) :
    ((F.map₂HomotopyCategory c₁ c₂ c).map ((HomotopyCategory.quotient C₁ c₁).map f₁)).app
        ((HomotopyCategory.quotient C₂ c₂).obj K₂) =
      (HomotopyCategory.quotient D c).map (mapBifunctorMap f₁ (𝟙 K₂) F c) :=
  (rfl)

section MapBifunctorLeftUnitor

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
  simp [mapBifunctorLeftUnitor_inv_f, reassoc_of% h, reassoc_of% h']

@[reassoc]
lemma mapBifunctorLeftUnitor_naturality {K L : HomologicalComplex D c} (f : K ⟶ L)
    [HasMapBifunctor ((single C c 0).obj X) K F c]
    [HasMapBifunctor ((single C c 0).obj X) L F c] :
    mapBifunctorMap (𝟙 _) f F c ≫ (mapBifunctorLeftUnitor F X e L).hom =
      (mapBifunctorLeftUnitor F X e K).hom ≫ f := by
  rw [← cancel_mono (mapBifunctorLeftUnitor F X e L).inv, assoc, assoc, Iso.hom_inv_id,
    comp_id, mapBifunctorLeftUnitor_inv_naturality, Iso.hom_inv_id_assoc]

end MapBifunctorLeftUnitor

section LeftUnitor

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [HasZeroObject C] [Preadditive D]
  (F : C ⥤ D ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  (X : C) (e : F.obj X ≅ 𝟭 D)
  {I : Type*} [AddMonoid I] [DecidableEq I] (c : ComplexShape I) [c.TensorSigns]
  [∀ (K₁ : HomologicalComplex C c) (K₂ : HomologicalComplex D c),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F c]

open HomologicalComplex

/-- On homotopy categories, the complex `X[0]` acts as the identity functor when
`e : F.obj X ≅ 𝟭 D`. -/
def map₂HomotopyCategoryLeftUnitor :
    (F.map₂HomotopyCategory c c c).obj
        ((HomotopyCategory.quotient C c).obj ((single C c 0).obj X)) ≅
      𝟭 (HomotopyCategory D c) :=
  CategoryTheory.Quotient.natIsoLift _
    (NatIso.ofComponents (F := HomotopyCategory.quotient D c ⋙ _)
      (G := HomotopyCategory.quotient D c ⋙ 𝟭 _)
      (fun K ↦ (HomotopyCategory.quotient D c).mapIso (mapBifunctorLeftUnitor F X e K))
      (fun f ↦ ((HomotopyCategory.quotient D c).map_comp _ _).symm.trans
        (((HomotopyCategory.quotient D c).congr_map
          (mapBifunctorLeftUnitor_naturality F X e f)).trans
          ((HomotopyCategory.quotient D c).map_comp _ _))))

@[simp]
lemma map₂HomotopyCategoryLeftUnitor_hom_app (K : HomologicalComplex D c) :
    (F.map₂HomotopyCategoryLeftUnitor X e c).hom.app ((HomotopyCategory.quotient D c).obj K) =
      (HomotopyCategory.quotient D c).map (mapBifunctorLeftUnitor F X e K).hom :=
  (rfl)

@[simp]
lemma map₂HomotopyCategoryLeftUnitor_inv_app (K : HomologicalComplex D c) :
    (F.map₂HomotopyCategoryLeftUnitor X e c).inv.app ((HomotopyCategory.quotient D c).obj K) =
      (HomotopyCategory.quotient D c).map (mapBifunctorLeftUnitor F X e K).inv :=
  (rfl)

end LeftUnitor

section Associator

variable {C₁ C₂ C₃ C₁₂ C₂₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* C₁₂] [Category* C₂₃] [Category* C₄]
  [Preadditive C₁] [Preadditive C₂] [Preadditive C₃] [Preadditive C₁₂] [Preadditive C₂₃]
  [Preadditive C₄]
  {F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂} {G : C₁₂ ⥤ C₃ ⥤ C₄} {F : C₁ ⥤ C₂₃ ⥤ C₄} {G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃}
  [F₁₂.Additive] [∀ X, (F₁₂.obj X).Additive] [G.Additive] [∀ X, (G.obj X).Additive]
  [F.Additive] [∀ X, (F.obj X).Additive] [G₂₃.Additive] [∀ X, (G₂₃.obj X).Additive]
  (associator : bifunctorComp₁₂ F₁₂ G ≅ bifunctorComp₂₃ F G₂₃)
  {ι₁ ι₂ ι₃ ι₁₂ ι₂₃ ι₄ : Type*} [DecidableEq ι₁₂] [DecidableEq ι₂₃] [DecidableEq ι₄]
  (c₁ : ComplexShape ι₁) (c₂ : ComplexShape ι₂) (c₃ : ComplexShape ι₃)
  (c₁₂ : ComplexShape ι₁₂) (c₂₃ : ComplexShape ι₂₃) (c₄ : ComplexShape ι₄)
  [TotalComplexShape c₁ c₂ c₁₂] [TotalComplexShape c₁₂ c₃ c₄]
  [TotalComplexShape c₂ c₃ c₂₃] [TotalComplexShape c₁ c₂₃ c₄]
  [ComplexShape.Associative c₁ c₂ c₃ c₁₂ c₂₃ c₄]
  [∀ (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂),
    HomologicalComplex.HasMapBifunctor K₁ K₂ F₁₂ c₁₂]
  [∀ (K₂ : HomologicalComplex C₂ c₂) (K₃ : HomologicalComplex C₃ c₃),
    HomologicalComplex.HasMapBifunctor K₂ K₃ G₂₃ c₂₃]
  [∀ (K₁₂ : HomologicalComplex C₁₂ c₁₂) (K₃ : HomologicalComplex C₃ c₃),
    HomologicalComplex.HasMapBifunctor K₁₂ K₃ G c₄]
  [∀ (K₁ : HomologicalComplex C₁ c₁) (K₂₃ : HomologicalComplex C₂₃ c₂₃),
    HomologicalComplex.HasMapBifunctor K₁ K₂₃ F c₄]
  [∀ (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂)
    (K₃ : HomologicalComplex C₃ c₃),
    HomologicalComplex.HasGoodTrifunctor₁₂Obj F₁₂ G K₁ K₂ K₃ c₁₂ c₄]
  [∀ (K₁ : HomologicalComplex C₁ c₁) (K₂ : HomologicalComplex C₂ c₂)
    (K₃ : HomologicalComplex C₃ c₃),
    HomologicalComplex.HasGoodTrifunctor₂₃Obj F G₂₃ K₁ K₂ K₃ c₁₂ c₂₃ c₄]

open HomologicalComplex

/-- On homotopy categories, acting by the total complex `mapBifunctor K₁ K₂ F₁₂ c₁₂` through `G`
is isomorphic to acting first by `K₂` through `G₂₃` and then by `K₁` through `F`, given an
`associator` between the two composite trifunctors. The components are the images of Mathlib's
`HomologicalComplex.mapBifunctorAssociator`. -/
def map₂HomotopyCategoryAssociator (K₁ : HomologicalComplex C₁ c₁)
    (K₂ : HomologicalComplex C₂ c₂) :
    (G.map₂HomotopyCategory c₁₂ c₃ c₄).obj
        ((HomotopyCategory.quotient C₁₂ c₁₂).obj (mapBifunctor K₁ K₂ F₁₂ c₁₂)) ≅
      (G₂₃.map₂HomotopyCategory c₂ c₃ c₂₃).obj ((HomotopyCategory.quotient C₂ c₂).obj K₂) ⋙
        (F.map₂HomotopyCategory c₁ c₂₃ c₄).obj ((HomotopyCategory.quotient C₁ c₁).obj K₁) :=
  CategoryTheory.Quotient.natIsoLift _
    (NatIso.ofComponents (F := HomotopyCategory.quotient C₃ c₃ ⋙ _)
      (G := HomotopyCategory.quotient C₃ c₃ ⋙ _)
      (fun K₃ ↦ (HomotopyCategory.quotient C₄ c₄).mapIso
        (mapBifunctorAssociator associator K₁ K₂ K₃ c₁₂ c₂₃ c₄))
      (fun f ↦ ((HomotopyCategory.quotient C₄ c₄).map_comp _ _).symm.trans
        (((HomotopyCategory.quotient C₄ c₄).congr_map (by
          have h := TauCeti.HomologicalComplex.mapBifunctorAssociator_naturality associator
            c₁₂ c₂₃ c₄ (𝟙 K₁) (𝟙 K₂) f
          rw [mapBifunctorMap_id] at h
          exact h)).trans
          ((HomotopyCategory.quotient C₄ c₄).map_comp _ _))))

@[simp]
lemma map₂HomotopyCategoryAssociator_hom_app (K₁ : HomologicalComplex C₁ c₁)
    (K₂ : HomologicalComplex C₂ c₂) (K₃ : HomologicalComplex C₃ c₃) :
    (map₂HomotopyCategoryAssociator associator c₁ c₂ c₃ c₁₂ c₂₃ c₄ K₁ K₂).hom.app
        ((HomotopyCategory.quotient C₃ c₃).obj K₃) =
      (HomotopyCategory.quotient C₄ c₄).map
        (mapBifunctorAssociator associator K₁ K₂ K₃ c₁₂ c₂₃ c₄).hom :=
  (rfl)

@[simp]
lemma map₂HomotopyCategoryAssociator_inv_app (K₁ : HomologicalComplex C₁ c₁)
    (K₂ : HomologicalComplex C₂ c₂) (K₃ : HomologicalComplex C₃ c₃) :
    (map₂HomotopyCategoryAssociator associator c₁ c₂ c₃ c₁₂ c₂₃ c₄ K₁ K₂).inv.app
        ((HomotopyCategory.quotient C₃ c₃).obj K₃) =
      (HomotopyCategory.quotient C₄ c₄).map
        (mapBifunctorAssociator associator K₁ K₂ K₃ c₁₂ c₂₃ c₄).inv :=
  (rfl)

end Associator

end CategoryTheory.Functor
