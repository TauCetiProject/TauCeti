/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Full subcategories: lifts, successive restrictions, and basic API

This file collects general facts about the full subcategory of an object property, beyond those
in Mathlib's `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`.

## Lifts through a full subcategory

* `CategoryTheory.ObjectProperty.lift_comp_ι`: a lift through a full subcategory, followed by the
  inclusion, is the original functor.
* `CategoryTheory.ObjectProperty.map_hom_of_comp_ι_eq`: a functor `G` with `G ⋙ P.ι = F` acts on
  morphisms as `F`, up to the identifications of the underlying objects.
* `CategoryTheory.ObjectProperty.essSurj_lift_iff`: a lift of `F` through a full subcategory is
  essentially surjective exactly when the property is contained in the essential image of `F`.

## Morphisms and instances

* `CategoryTheory.ObjectProperty.homMk_eta` and `CategoryTheory.ObjectProperty.homMk_comp`:
  `homMk` of the underlying morphism is the morphism itself, and `homMk` preserves composites.
* `CategoryTheory.ObjectProperty.mono_homMk`: `homMk` of a monomorphism of the ambient category is
  a monomorphism of the full subcategory.
* `CategoryTheory.ObjectProperty.FullSubcategory.isGroupoid`: a full subcategory of a groupoid is a
  groupoid.
* `CategoryTheory.ObjectProperty.ιOfLE_additive`: the inclusion of a smaller property into a
  larger one is additive.
* `CategoryTheory.ObjectProperty.hasFiniteBiproducts_fullSubcategory`: a full subcategory closed
  under finite products of a preadditive category with finite biproducts has finite biproducts.

## Successive restrictions

Restricting a category first to objects satisfying `P`, and then to those whose underlying
objects satisfy `Q`, is canonically equivalent to restricting to `P ⊓ Q`
(`CategoryTheory.ObjectProperty.iteratedFullSubcategoryEquivalence`). The comparison
leaves underlying objects and morphisms unchanged, commutes with the inclusions, and is
linear whenever the ambient category is linear. No closure under isomorphisms is needed.
The construction uses Mathlib's `ObjectProperty.lift` and `ObjectProperty.ιOfLE`.
-/

public section

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category* C] (P Q : ObjectProperty C)

/-- A full subcategory of a groupoid is a groupoid, without any closure condition on objects. -/
instance FullSubcategory.isGroupoid [IsGroupoid C] : IsGroupoid P.FullSubcategory :=
  isGroupoid_of_reflects_iso P.ι

/-- The lift of a functor through a full subcategory, followed by the inclusion, is the original
functor. This is the equality form of Mathlib's isomorphism
`CategoryTheory.ObjectProperty.liftCompιIso`. Use it where an isomorphism does not suffice: to
rewrite a composite of functors, or to supply the hypothesis of
`CategoryTheory.ObjectProperty.map_hom_of_comp_ι_eq` for a functor defined as a lift. -/
theorem lift_comp_ι {E : Type*} [Category* E] (F : E ⥤ C) (hF : ∀ A, P (F.obj A)) :
    P.lift F hF ⋙ P.ι = F :=
  Functor.ext (P.ι_obj_lift_obj F hF) fun _ _ f ↦ by
    rw [Functor.comp_map, P.ι_obj_lift_map F hF f]
    simp

variable {P} in
/-- A functor `G` lifting `F` through a full subcategory, in the sense that `G ⋙ P.ι = F`, acts
on morphisms as `F`, up to the identifications `hA` and `hB` of the underlying objects. For
`G = P.lift F hF`, or a functor defined as such a lift, the hypothesis is `lift_comp_ι`. -/
theorem map_hom_of_comp_ι_eq {E : Type*} [Category* E] {F : E ⥤ C} {G : E ⥤ P.FullSubcategory}
    (hG : G ⋙ P.ι = F) {A B : E} (f : A ⟶ B) (hA : (G.obj A).obj = F.obj A)
    (hB : (G.obj B).obj = F.obj B) :
    (G.map f).hom = eqToHom hA ≫ F.map f ≫ eqToHom hB.symm := by
  simpa only [Functor.comp_map, Functor.comp_obj, ι_map, ι_obj] using Functor.congr_hom hG f

/-- The lift of a functor through a full subcategory is essentially surjective exactly when every
object satisfying the property lies in the essential image of the original functor. -/
theorem essSurj_lift_iff {E : Type*} [Category* E] (F : E ⥤ C) (hF : ∀ A, P (F.obj A)) :
    (P.lift F hF).EssSurj ↔ P ≤ F.essImage := by
  refine ⟨fun _ Y hY ↦ ?_, fun hPF ↦ ⟨fun Y ↦ ?_⟩⟩
  · exact ⟨_, ⟨P.ι.mapIso ((P.lift F hF).objObjPreimageIso ⟨Y, hY⟩)⟩⟩
  · obtain ⟨A, ⟨e⟩⟩ := hPF _ Y.property
    exact ⟨A, ⟨P.isoMk e⟩⟩

variable {P} in
/-- A morphism of a full subcategory is `homMk` of its underlying morphism. -/
@[simp]
theorem homMk_eta {X Y : P.FullSubcategory} (f : X ⟶ Y) : homMk f.hom = f :=
  rfl

variable {P} in
/-- `homMk` of a composite is the composite of the `homMk`s. This is useful when `homMk (· ≫ ·)`
appears under a functor. -/
theorem homMk_comp {X Y Z : P.FullSubcategory} (f : X.obj ⟶ Y.obj) (g : Y.obj ⟶ Z.obj) :
    homMk (f ≫ g) = homMk f ≫ homMk g :=
  rfl

variable {P} in
/-- A morphism of a full subcategory is a monomorphism as soon as it is one in the ambient
category. -/
instance mono_homMk {X Y : P.FullSubcategory} (f : X.obj ⟶ Y.obj) [Mono f] : Mono (homMk f) :=
  P.ι.mono_of_mono_map (by simpa only [ι_map, homMk_hom] using (inferInstance : Mono f))

/-- Two successive full-subcategory restrictions agree with restriction to the intersection.
The comparison and its inverse leave the underlying objects and morphisms unchanged. -/
-- The object and functor data are exposed so that morphisms, including the identity
-- lineators for restricted actions, have definitionally the same endpoints in both presentations.
@[expose]
def iteratedFullSubcategoryEquivalence :
    (Q.inverseImage P.ι).FullSubcategory ≌ (P ⊓ Q).FullSubcategory where
  functor := (P ⊓ Q).lift ((Q.inverseImage P.ι).ι ⋙ P.ι)
    (fun X => ⟨X.obj.property, X.property⟩)
  inverse := (Q.inverseImage P.ι).lift (ιOfLE (P := P ⊓ Q) inf_le_left)
    (fun X => X.property.2)
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- Flattening the successive restrictions leaves the underlying object unchanged. -/
@[simp]
lemma iteratedFullSubcategoryEquivalence_functor_obj_obj
    (X : (Q.inverseImage P.ι).FullSubcategory) :
    ((P.iteratedFullSubcategoryEquivalence Q).functor.obj X).obj = X.obj.obj :=
  rfl

/-- Flattening the successive restrictions leaves the underlying morphism unchanged. -/
@[simp]
lemma iteratedFullSubcategoryEquivalence_functor_map_hom
    {X Y : (Q.inverseImage P.ι).FullSubcategory} (f : X ⟶ Y) :
    ((P.iteratedFullSubcategoryEquivalence Q).functor.map f).hom = f.hom.hom :=
  rfl

/-- Nesting an intersection object recovers its object in the first full subcategory. -/
@[simp]
lemma iteratedFullSubcategoryEquivalence_inverse_obj_obj
    (X : (P ⊓ Q).FullSubcategory) :
    ((P.iteratedFullSubcategoryEquivalence Q).inverse.obj X).obj =
      (ιOfLE (P := P ⊓ Q) inf_le_left).obj X :=
  rfl

/-- Nesting an intersection morphism recovers its morphism in the first full subcategory. -/
@[simp]
lemma iteratedFullSubcategoryEquivalence_inverse_map_hom
    {X Y : (P ⊓ Q).FullSubcategory} (f : X ⟶ Y) :
    ((P.iteratedFullSubcategoryEquivalence Q).inverse.map f).hom =
      (ιOfLE (P := P ⊓ Q) inf_le_left).map f :=
  rfl

/-- The forward comparison commutes with inclusion in the ambient category. -/
lemma iteratedFullSubcategoryEquivalence_functor_comp_ι :
    (P.iteratedFullSubcategoryEquivalence Q).functor ⋙ (P ⊓ Q).ι =
      (Q.inverseImage P.ι).ι ⋙ P.ι :=
  rfl

/-- The inverse comparison commutes with inclusion in the first full subcategory. -/
lemma iteratedFullSubcategoryEquivalence_inverse_comp_ι :
    (P.iteratedFullSubcategoryEquivalence Q).inverse ⋙ (Q.inverseImage P.ι).ι =
      ιOfLE (P := P ⊓ Q) inf_le_left :=
  rfl

/-- The unit comparison is the identity on the underlying object. -/
@[simp]
lemma iteratedFullSubcategoryEquivalence_unitIso_hom_app_hom_hom
    (X : (Q.inverseImage P.ι).FullSubcategory) :
    ((P.iteratedFullSubcategoryEquivalence Q).unitIso.hom.app X).hom.hom = 𝟙 X.obj.obj :=
  rfl

/-- The counit comparison is the identity on the underlying object. -/
@[simp]
lemma iteratedFullSubcategoryEquivalence_counitIso_hom_app_hom
    (X : (P ⊓ Q).FullSubcategory) :
    ((P.iteratedFullSubcategoryEquivalence Q).counitIso.hom.app X).hom = 𝟙 X.obj :=
  rfl

/-- The inverse unit comparison is the identity on the underlying object. -/
@[simp]
lemma iteratedFullSubcategoryEquivalence_unitIso_inv_app_hom_hom
    (X : (Q.inverseImage P.ι).FullSubcategory) :
    ((P.iteratedFullSubcategoryEquivalence Q).unitIso.inv.app X).hom.hom = 𝟙 X.obj.obj :=
  rfl

/-- The inverse counit comparison is the identity on the underlying object. -/
@[simp]
lemma iteratedFullSubcategoryEquivalence_counitIso_inv_app_hom
    (X : (P ⊓ Q).FullSubcategory) :
    ((P.iteratedFullSubcategoryEquivalence Q).counitIso.inv.app X).hom = 𝟙 X.obj :=
  rfl

section Linear

variable [Preadditive C]

variable {P Q} in
/-- The inclusion of a smaller object property into a larger one is an additive functor: followed
by the faithful additive inclusion of the larger one, it is the additive inclusion of the smaller
one. -/
instance ιOfLE_additive (h : P ≤ Q) : (ιOfLE h).Additive :=
  have := Functor.additive_of_iso (ιOfLECompιIso h).symm
  Functor.additive_of_comp_faithful _ Q.ι

/-- The comparison between successive restrictions and the intersection is additive. -/
instance iteratedFullSubcategoryEquivalence_functor_additive :
    (P.iteratedFullSubcategoryEquivalence Q).functor.Additive :=
  inferInstanceAs ((P ⊓ Q).lift ((Q.inverseImage P.ι).ι ⋙ P.ι) _).Additive

/-- The comparison between successive restrictions and the intersection is scalar-linear. -/
instance iteratedFullSubcategoryEquivalence_functor_linear (R : Type*) [Semiring R]
    [Linear R C] : (P.iteratedFullSubcategoryEquivalence Q).functor.Linear R where
  map_smul f r := by ext; rfl

end Linear

section Biproducts

open Limits

variable [Preadditive C] [HasFiniteBiproducts C]

/-- A full subcategory of a preadditive category with finite biproducts, closed under finite
products, has finite biproducts. -/
instance hasFiniteBiproducts_fullSubcategory [P.IsClosedUnderFiniteProducts] :
    HasFiniteBiproducts P.FullSubcategory :=
  .of_hasFiniteProducts

end Biproducts

end CategoryTheory.ObjectProperty
