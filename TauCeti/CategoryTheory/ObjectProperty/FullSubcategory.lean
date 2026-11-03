/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Successive full-subcategory restrictions

Restricting a category first to objects satisfying `P`, and then to those whose underlying
objects satisfy `Q`, is canonically equivalent to restricting to `P ⊓ Q`. The comparison
leaves underlying objects and morphisms unchanged, commutes with the inclusions, and is
linear whenever the ambient category is linear. No closure under isomorphisms is needed.

The construction uses Mathlib's `ObjectProperty.lift` and `ObjectProperty.ιOfLE`.
-/

public section

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category* C] (P Q : ObjectProperty C)

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

/-- The comparison between successive restrictions and the intersection is additive. -/
instance iteratedFullSubcategoryEquivalence_functor_additive :
    (P.iteratedFullSubcategoryEquivalence Q).functor.Additive :=
  inferInstanceAs ((P ⊓ Q).lift ((Q.inverseImage P.ι).ι ⋙ P.ι) _).Additive

/-- The comparison between successive restrictions and the intersection is scalar-linear. -/
instance iteratedFullSubcategoryEquivalence_functor_linear (R : Type*) [Semiring R]
    [Linear R C] : (P.iteratedFullSubcategoryEquivalence Q).functor.Linear R where
  map_smul f r := by ext; rfl

end Linear

end CategoryTheory.ObjectProperty
