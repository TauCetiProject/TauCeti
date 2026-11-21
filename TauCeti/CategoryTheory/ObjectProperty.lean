/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.ObjectProperty.FiniteProducts
public import TauCeti.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Object properties: transport along equivalences, and closure properties

This file contains general lemmas about object properties: transporting them along an
equivalence, comparing Mathlib's closure type classes with one another in the presence of a
terminal object and of binary biproducts, smallness of full subcategories, and additivity of the
standard functors between full subcategories.

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
* `CategoryTheory.ObjectProperty.homMk_eta` and `CategoryTheory.ObjectProperty.homMk_comp`:
  `homMk` of the underlying morphism is the morphism itself, and `homMk` preserves composites.
* `CategoryTheory.ObjectProperty.lift_map_hom_of_eq`: a functor `G` with `G ⋙ P.ι = F` acts on
  morphisms as `F`, up to the identifications of objects.
* `CategoryTheory.ObjectProperty.essSurj_lift_iff`: a lift through a full subcategory is
  essentially surjective exactly when the property is contained in the essential image.
* `CategoryTheory.ObjectProperty.essentiallySmall_of_ambient`: every property in an essentially
  small category is essentially small.
* `CategoryTheory.ObjectProperty.ιOfLE_additive`: the inclusion of a smaller property into a larger
  one is additive.
* `CategoryTheory.Equivalence.congrFullSubcategory_functor_additive` and
  `CategoryTheory.Equivalence.congrFullSubcategory_inverse_additive`: an additive equivalence
  restricts to an additive equivalence between corresponding full subcategories.
* `CategoryTheory.Equivalence.congrFullSubcategory_functor_comp_ι` and
  `CategoryTheory.Equivalence.congrFullSubcategory_inverse_comp_ι`: the restricted functors,
  followed by the inclusions, are the inclusions followed by the original functors.
* `CategoryTheory.Equivalence.congrFullSubcategory_functor_obj_obj`,
  `CategoryTheory.Equivalence.congrFullSubcategory_functor_map_hom` and their `inverse`
  counterparts: the restricted functors evaluated on objects and morphisms, for deriving the
  evaluation lemmas of any equivalence defined as a `congrFullSubcategory`.
-/

public section

universe w u₁ v₁ u₂ v₂

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
isomorphisms.** This is `CategoryTheory.ObjectProperty.isClosedUnderIsomorphisms_of_isTerminal`
for the zero object supplied by `CategoryTheory.ObjectProperty.ContainsZero`, so that it applies
by type class inference alone. -/
theorem isClosedUnderIsomorphisms_of_containsZero {C : Type u₁} [Category.{v₁} C]
    (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderBinaryProducts] :
    P.IsClosedUnderIsomorphisms := by
  obtain ⟨Z, hZ, hZP⟩ := P.exists_prop_of_containsZero
  exact P.isClosedUnderIsomorphisms_of_isTerminal hZ.isTerminal hZP

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

/-- A morphism of a full subcategory is `homMk` of its underlying morphism. -/
@[simp]
theorem homMk_eta {C : Type u₁} [Category.{v₁} C] {P : ObjectProperty C}
    {X Y : P.FullSubcategory} (f : X ⟶ Y) : homMk f.hom = f :=
  rfl

/-- `homMk` of a composite is the composite of the `homMk`s. This is useful when `homMk (· ≫ ·)`
appears under a functor. -/
theorem homMk_comp {C : Type u₁} [Category.{v₁} C] {P : ObjectProperty C}
    {X Y Z : P.FullSubcategory} (f : X.obj ⟶ Y.obj) (g : Y.obj ⟶ Z.obj) :
    homMk (f ≫ g) = homMk f ≫ homMk g :=
  rfl

/-- A functor `G` lifting `F` through a full subcategory, in the sense that `G ⋙ P.ι = F`, acts
on morphisms as `F`, up to the identifications of the underlying objects. This applies in
particular to `G = P.lift F hF`, through `lift_comp_ι`, and to a functor defined as such a lift. -/
theorem lift_map_hom_of_eq {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {P : ObjectProperty D} {F : C ⥤ D} {G : C ⥤ P.FullSubcategory}
    (hG : G ⋙ P.ι = F) {A B : C} (f : A ⟶ B) (hA : (G.obj A).obj = F.obj A)
    (hB : (G.obj B).obj = F.obj B) :
    (G.map f).hom = eqToHom hA ≫ F.map f ≫ eqToHom hB.symm :=
  Functor.congr_hom hG f

/-- The lift of a functor through a full subcategory is essentially surjective exactly when every
object satisfying the property lies in the essential image of the original functor. -/
theorem essSurj_lift_iff {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (P : ObjectProperty D) (F : C ⥤ D) (hF : ∀ A, P (F.obj A)) :
    (P.lift F hF).EssSurj ↔ P ≤ F.essImage := by
  refine ⟨fun _ Y hY ↦ ?_, fun hPF ↦ ⟨fun Y ↦ ?_⟩⟩
  · exact ⟨_, ⟨P.ι.mapIso ((P.lift F hF).objObjPreimageIso ⟨Y, hY⟩)⟩⟩
  · obtain ⟨A, ⟨e⟩⟩ := hPF _ Y.property
    exact ⟨A, ⟨P.isoMk e⟩⟩

end ObjectProperty

namespace Equivalence

/-- The forward functor on corresponding full subcategories, followed by the inclusion, is the
inclusion followed by the original functor. -/
theorem congrFullSubcategory_functor_comp_ι
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {P : ObjectProperty C} {Q : ObjectProperty D} [Q.IsClosedUnderIsomorphisms]
    (e : C ≌ D) (h : Q.inverseImage e.functor = P) :
    (e.congrFullSubcategory h).functor ⋙ Q.ι = P.ι ⋙ e.functor := by
  rw [congrFullSubcategory_functor]
  exact ObjectProperty.lift_comp_ι ..

/-- The inverse functor on corresponding full subcategories, followed by the inclusion, is the
inclusion followed by the original inverse. -/
theorem congrFullSubcategory_inverse_comp_ι
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {P : ObjectProperty C} {Q : ObjectProperty D} [Q.IsClosedUnderIsomorphisms]
    (e : C ≌ D) (h : Q.inverseImage e.functor = P) :
    (e.congrFullSubcategory h).inverse ⋙ P.ι = Q.ι ⋙ e.inverse := by
  rw [congrFullSubcategory_inverse]
  exact ObjectProperty.lift_comp_ι ..

section Evaluation

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {P : ObjectProperty C} {Q : ObjectProperty D} [Q.IsClosedUnderIsomorphisms]
  (e : C ≌ D) (h : Q.inverseImage e.functor = P)

/-- The forward functor on corresponding full subcategories acts on objects as the original
functor. Not a simp lemma: `congrFullSubcategory_functor` already unfolds the left-hand side. -/
theorem congrFullSubcategory_functor_obj_obj (X : P.FullSubcategory) :
    ((e.congrFullSubcategory h).functor.obj X).obj = e.functor.obj X.obj := by simp

/-- The forward functor on corresponding full subcategories acts on morphisms as the original
functor, up to the identifications of `congrFullSubcategory_functor_obj_obj`. -/
theorem congrFullSubcategory_functor_map_hom {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    ((e.congrFullSubcategory h).functor.map f).hom =
      eqToHom (e.congrFullSubcategory_functor_obj_obj h X) ≫ e.functor.map f.hom ≫
        eqToHom (e.congrFullSubcategory_functor_obj_obj h Y).symm := by
  simpa only [Functor.comp_map, ObjectProperty.ι_map] using
    Functor.congr_hom (e.congrFullSubcategory_functor_comp_ι h) f

/-- The inverse functor on corresponding full subcategories acts on objects as the original
inverse. Not a simp lemma: `congrFullSubcategory_inverse` already unfolds the left-hand side. -/
theorem congrFullSubcategory_inverse_obj_obj (Y : Q.FullSubcategory) :
    ((e.congrFullSubcategory h).inverse.obj Y).obj = e.inverse.obj Y.obj := by simp

/-- The inverse functor on corresponding full subcategories acts on morphisms as the original
inverse, up to the identifications of `congrFullSubcategory_inverse_obj_obj`. -/
theorem congrFullSubcategory_inverse_map_hom {X Y : Q.FullSubcategory} (f : X ⟶ Y) :
    ((e.congrFullSubcategory h).inverse.map f).hom =
      eqToHom (e.congrFullSubcategory_inverse_obj_obj h X) ≫ e.inverse.map f.hom ≫
        eqToHom (e.congrFullSubcategory_inverse_obj_obj h Y).symm := by
  simpa only [Functor.comp_map, ObjectProperty.ι_map] using
    Functor.congr_hom (e.congrFullSubcategory_inverse_comp_ι h) f

end Evaluation

/-- The functor of an equivalence restricted to corresponding full subcategories is additive. -/
instance congrFullSubcategory_functor_additive
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    {P : ObjectProperty C} {Q : ObjectProperty D} [Q.IsClosedUnderIsomorphisms]
    (e : C ≌ D) [e.functor.Additive] (h : Q.inverseImage e.functor = P) :
    (e.congrFullSubcategory h).functor.Additive := by
  rw [congrFullSubcategory_functor]
  infer_instance

/-- The inverse of an equivalence restricted to corresponding full subcategories is additive. -/
instance congrFullSubcategory_inverse_additive
    {C : Type u₁} [Category.{v₁} C] [Preadditive C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D]
    {P : ObjectProperty C} {Q : ObjectProperty D} [Q.IsClosedUnderIsomorphisms]
    (e : C ≌ D) [e.inverse.Additive] (h : Q.inverseImage e.functor = P) :
    (e.congrFullSubcategory h).inverse.Additive := by
  rw [congrFullSubcategory_inverse]
  infer_instance

end Equivalence

end CategoryTheory
