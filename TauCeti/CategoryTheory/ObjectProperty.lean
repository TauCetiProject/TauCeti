/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Object properties: transport along equivalences, and closure properties

This file contains general lemmas about object properties: transporting them along an
equivalence, comparing Mathlib's closure type classes with one another in the presence of a
zero object and of binary biproducts, smallness of full subcategories, and functors between full
subcategories.

## Main declarations

* `CategoryTheory.ObjectProperty.inverseImage_functor_inverseImage_inverse`: pulling an
  isomorphism-invariant property backward along both functors of an equivalence recovers it.
* `CategoryTheory.ObjectProperty.isClosedUnderIsomorphisms_of_containsZero`: a property holding
  for a zero object and closed under binary products is closed under isomorphisms.
* `CategoryTheory.ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod`: for a replete
  property in a category with binary biproducts, closure under binary products only has to be
  checked on biproducts.
* `CategoryTheory.ObjectProperty.prop_biprod_of_isClosedUnderBinaryProducts`: a property closed
  under binary products holds for binary biproducts, with `X ⊞ Y` as the syntactic form of the
  conclusion.
* `CategoryTheory.ObjectProperty.essentiallySmall_of_ambient`: every property in an essentially
  small category is essentially small.
* `CategoryTheory.ObjectProperty.mapFullSubcategory`: restriction of a functor carrying one object
  property into another to their full subcategories.
* `CategoryTheory.ObjectProperty.ιOfLE_additive`: the inclusion of a smaller property into a larger
  one is additive.
* `CategoryTheory.Equivalence.congrFullSubcategory_functor_additive` and
  `CategoryTheory.Equivalence.congrFullSubcategory_inverse_additive`: an additive equivalence
  restricts to an additive equivalence between corresponding full subcategories.
-/

public section

universe w u₁ v₁ u₂ v₂ u₃ v₃

namespace CategoryTheory

open Limits

namespace ObjectProperty

/-- Pulling an isomorphism-invariant object property backward along both functors of an
equivalence recovers the original property. -/
theorem inverseImage_functor_inverseImage_inverse
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] (e : C ≌ D) :
    (P.inverseImage e.inverse).inverseImage e.functor = P := by
  ext X
  exact (P.prop_iff_of_iso (e.unitIso.app X)).symm

/-- **A property holding for a zero object and closed under binary products is closed under
isomorphisms.** An isomorphism `e : X ≅ Y` exhibits `Y` as a product of a zero object with `X`,
the two projections being the zero morphism and `e.inv`.

Mathlib's `CategoryTheory.ObjectProperty.IsClosedUnderBinaryProducts.closedUnderIsomorphisms` is
the same argument run on a terminal object, but it assumes closure under the empty limit, which
`CategoryTheory.ObjectProperty.ContainsZero` — the property for *one* zero object — does not
supply before repleteness is known. -/
theorem isClosedUnderIsomorphisms_of_containsZero {C : Type u₁} [Category.{v₁} C]
    (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderBinaryProducts] :
    P.IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    obtain ⟨Z, hZ, hZP⟩ := P.exists_prop_of_containsZero
    let B : BinaryFan Z X := BinaryFan.mk (hZ.from_ Y) e.inv
    have hB : IsLimit B := BinaryFan.IsLimit.mk B (fun _ g => g ≫ e.hom)
      (fun _ _ => hZ.eq_of_tgt _ _)
      (fun _ _ => by simp [B])
      (fun _ _ _ _ hg => by simpa [B] using congrArg (fun k => k ≫ e.hom) hg)
    exact P.prop_of_isLimit_binaryFan hB hZP hX

/-- **For a replete property, closure under binary products only has to be checked on
biproducts**, since in a category with binary biproducts every binary product is one. -/
theorem isClosedUnderBinaryProducts_of_prop_biprod {C : Type u₁} [Category.{v₁} C]
    [HasZeroMorphisms C] [HasBinaryBiproducts C] (P : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms] (h : ∀ X Y : C, P X → P Y → P (X ⊞ Y)) :
    P.IsClosedUnderBinaryProducts := by
  refine IsClosedUnderLimitsOfShape.mk' ?_
  rintro _ ⟨F, hF⟩
  refine P.prop_of_iso ?_ (h _ _ (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩))
  exact (biprod.isoProd _ _).trans (HasLimit.isoOfNatIso (diagramIsoPair F)).symm

/-- **A property closed under binary products holds for binary biproducts.** In a category with
binary biproducts the biproduct is a binary product, so this is
`CategoryTheory.ObjectProperty.prop_of_isLimit_binaryFan` applied to
`CategoryTheory.Limits.BinaryBiproduct.isLimit`; naming it keeps the index of the conclusion
syntactically `X ⊞ Y`, which matters when the conclusion is the type index of a dependent
family. -/
theorem prop_biprod_of_isClosedUnderBinaryProducts {C : Type u₁} [Category.{v₁} C]
    [HasZeroMorphisms C] (P : ObjectProperty C) [P.IsClosedUnderBinaryProducts]
    {X Y : C} [HasBinaryBiproduct X Y] (hX : P X) (hY : P Y) : P (X ⊞ Y) :=
  P.prop_of_isLimit_binaryFan (BinaryBiproduct.isLimit X Y) hX hY

/-- Every object property in an essentially small category is essentially small. This supplies
the smallness instance for its full subcategory through Mathlib's object-property API. -/
instance essentiallySmall_of_ambient {C : Type u₁} [Category.{v₁} C]
    [CategoryTheory.EssentiallySmall.{w} C] (P : ObjectProperty C) :
    ObjectProperty.EssentiallySmall.{w} P :=
  ObjectProperty.EssentiallySmall.of_le.{w} (Q := (⊤ : ObjectProperty C)) le_top

/-- The inclusion of a smaller object property into a larger one is an additive functor: both
categories carry the addition of the ambient one. -/
instance ιOfLE_additive {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {P P' : ObjectProperty C} (h : P ≤ P') : (ObjectProperty.ιOfLE h).Additive where
  map_add := rfl

/-- A functor carrying the objects satisfying `P` to objects satisfying `Q` restricts to a functor
between the corresponding full subcategories. -/
@[expose]
def mapFullSubcategory {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D)
    (h : P ≤ Q.inverseImage F) : P.FullSubcategory ⥤ Q.FullSubcategory where
  obj X := ⟨F.obj X.obj, h X.obj X.property⟩
  map f := homMk (F.map f.hom)

@[simp]
theorem mapFullSubcategory_obj_obj {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (P : ObjectProperty C) (Q : ObjectProperty D)
    (F : C ⥤ D) (h : P ≤ Q.inverseImage F) (X : P.FullSubcategory) :
    ((P.mapFullSubcategory Q F h).obj X).obj = F.obj X.obj := by
  rfl

@[simp]
theorem mapFullSubcategory_map_hom {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (P : ObjectProperty C) (Q : ObjectProperty D)
    (F : C ⥤ D) (h : P ≤ Q.inverseImage F) {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    ((P.mapFullSubcategory Q F h).map f).hom = F.map f.hom := by
  rfl

/-- Restriction to full subcategories commutes with their inclusion functors. -/
def mapFullSubcategoryCompιIso {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D)
    (h : P ≤ Q.inverseImage F) : P.mapFullSubcategory Q F h ⋙ Q.ι ≅ P.ι ⋙ F :=
  Iso.refl _

/-- Restricting the identity functor to a full subcategory gives the identity functor. -/
def mapFullSubcategoryIdIso {C : Type u₁} [Category.{v₁} C] (P : ObjectProperty C) :
    P.mapFullSubcategory P (𝟭 C) le_rfl ≅ 𝟭 P.FullSubcategory :=
  Iso.refl _

/-- Restriction to full subcategories commutes with composition of functors. -/
def mapFullSubcategoryCompIso
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {K : Type u₃} [Category.{v₃} K] (P : ObjectProperty C) (Q : ObjectProperty D)
    (R : ObjectProperty K) (F : C ⥤ D) (G : D ⥤ K) (hF : P ≤ Q.inverseImage F)
    (hG : Q ≤ R.inverseImage G) :
    P.mapFullSubcategory Q F hF ⋙ Q.mapFullSubcategory R G hG ≅
      P.mapFullSubcategory R (F ⋙ G) (fun X hX ↦ hG _ (hF X hX)) :=
  Iso.refl _

/-- Restricting an additive functor to full subcategories remains additive. -/
instance mapFullSubcategory_additive {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] (P : ObjectProperty C)
    (Q : ObjectProperty D) (F : C ⥤ D) [F.Additive] (h : P ≤ Q.inverseImage F) :
    (P.mapFullSubcategory Q F h).Additive where
  map_add := by
    intro X Y f g
    apply hom_ext
    exact F.map_add

end ObjectProperty

namespace Equivalence

/-- The canonical restriction of the forward functor agrees with the forward functor of Mathlib's
equivalence between corresponding full subcategories. -/
def mapFullSubcategoryIsoCongrFullSubcategoryFunctor
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {P : ObjectProperty C} {Q : ObjectProperty D} [Q.IsClosedUnderIsomorphisms]
    (e : C ≌ D) (h : Q.inverseImage e.functor = P) :
    P.mapFullSubcategory Q e.functor h.ge ≅ (e.congrFullSubcategory h).functor :=
  Iso.refl _

/-- A canonical restriction of the inverse functor agrees with the inverse functor of Mathlib's
equivalence between corresponding full subcategories. -/
def mapFullSubcategoryIsoCongrFullSubcategoryInverse
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {P : ObjectProperty C} {Q : ObjectProperty D} [Q.IsClosedUnderIsomorphisms]
    (e : C ≌ D) (h : Q.inverseImage e.functor = P) (hQP : Q ≤ P.inverseImage e.inverse) :
    Q.mapFullSubcategory P e.inverse hQP ≅ (e.congrFullSubcategory h).inverse :=
  Iso.refl _

/-- The functor of an equivalence restricted to corresponding full subcategories is additive. -/
instance congrFullSubcategory_functor_additive
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    {P : ObjectProperty C} {Q : ObjectProperty D} [Q.IsClosedUnderIsomorphisms]
    (e : C ≌ D) [e.functor.Additive] (h : Q.inverseImage e.functor = P) :
    (e.congrFullSubcategory h).functor.Additive where
  map_add := by
    intro X Y f g
    apply ObjectProperty.hom_ext
    exact e.functor.map_add

/-- The inverse of an equivalence restricted to corresponding full subcategories is additive. -/
instance congrFullSubcategory_inverse_additive
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    {P : ObjectProperty C} {Q : ObjectProperty D} [Q.IsClosedUnderIsomorphisms]
    (e : C ≌ D) [e.inverse.Additive] (h : Q.inverseImage e.functor = P) :
    (e.congrFullSubcategory h).inverse.Additive where
  map_add := by
    intro X Y f g
    apply ObjectProperty.hom_ext
    exact e.inverse.map_add

end Equivalence

end CategoryTheory
