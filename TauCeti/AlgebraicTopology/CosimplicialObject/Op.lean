/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Rev
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# Reversing cosimplicial objects

Precomposing with the covariant involution `SimplexCategory.rev` reverses a cosimplicial object:
its `i`th coface and codegeneracy become the original ones at the reversed index `i.rev`. This is
`CosimplicialObject.opFunctor`, the cosimplicial counterpart of Mathlib's
`SimplicialObject.opFunctor` (due to Joël Riou), whose conventions it follows. As there, the
terms of the reversed object are compared with the original ones through the identity
isomorphism `CosimplicialObject.opObjIso`, rather than by unfolding.

Since `SimplexCategory.rev` fixes every object, an augmentation can be kept unchanged; this gives
the reversal `CosimplicialObject.Augmented.opFunctor` of augmented cosimplicial objects. Reversal
is how a contraction splitting the *last* cofaces is brought to the form of an extra
codegeneracy, which splits the zeroth ones.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]

/-- The covariant involution of the category of cosimplicial objects that is induced by the
involution `SimplexCategory.rev : SimplexCategory ⥤ SimplexCategory`.
As for `SimplicialObject.opFunctor`, use the isomorphism `opObjIso` to compare
`(opFunctor.obj X).obj n` with `X.obj n`. -/
def opFunctor : CosimplicialObject C ⥤ CosimplicialObject C :=
  (Functor.whiskeringLeft _ _ _).obj SimplexCategory.rev

/-- The isomorphism `(opFunctor.obj X).obj n ≅ X.obj n` when `X` is a cosimplicial object. -/
def opObjIso {X : CosimplicialObject C} {n : SimplexCategory} :
    (opFunctor.obj X).obj n ≅ X.obj n := Iso.refl _

@[simp]
lemma opFunctor_map_app {X Y : CosimplicialObject C} (f : X ⟶ Y) (n : SimplexCategory) :
    (opFunctor.map f).app n = opObjIso.hom ≫ f.app n ≫ opObjIso.inv := by
  simp [opFunctor, opObjIso]

@[simp]
lemma opFunctor_obj_map (X : CosimplicialObject C) {n m : SimplexCategory} (f : n ⟶ m) :
    (opFunctor.obj X).map f = opObjIso.hom ≫ X.map (SimplexCategory.rev.map f) ≫ opObjIso.inv := by
  simp [opFunctor, opObjIso]

/-- The cofaces of the reversed cosimplicial object are the original cofaces at reversed
indices. -/
@[simp]
lemma opFunctor_obj_δ (X : CosimplicialObject C) {n : ℕ} (i : Fin (n + 2)) :
    (opFunctor.obj X).δ i = opObjIso.hom ≫ X.δ i.rev ≫ opObjIso.inv := by
  simp [CosimplicialObject.δ, SimplexCategory.rev_map_δ]

/-- The codegeneracies of the reversed cosimplicial object are the original codegeneracies at
reversed indices. -/
@[simp]
lemma opFunctor_obj_σ (X : CosimplicialObject C) {n : ℕ} (i : Fin (n + 1)) :
    (opFunctor.obj X).σ i = opObjIso.hom ≫ X.σ i.rev ≫ opObjIso.inv := by
  simp [CosimplicialObject.σ, SimplexCategory.rev_map_σ]

namespace Augmented

/-- The reversal of augmented cosimplicial objects: precompose the cosimplicial part with
`SimplexCategory.rev`, keeping the augmentation object and the augmentation maps. -/
def opFunctor : Augmented C ⥤ Augmented C where
  obj X :=
    { left := X.left
      right := CosimplicialObject.opFunctor.obj X.right
      hom := Functor.whiskerLeft SimplexCategory.rev X.hom }
  map f :=
    { left := f.left
      right := CosimplicialObject.opFunctor.map f.right
      w := by
        ext n
        exact congr_app f.w (SimplexCategory.rev.obj n) }

@[simp] lemma opFunctor_obj_left (X : Augmented C) :
    (opFunctor.obj X).left = X.left := (rfl)

@[simp] lemma opFunctor_obj_right (X : Augmented C) :
    (opFunctor.obj X).right = CosimplicialObject.opFunctor.obj X.right := (rfl)

/-- The augmentation of the reversed object is the original augmentation. -/
@[simp] lemma opFunctor_obj_hom_app (X : Augmented C) (n : SimplexCategory) :
    (opFunctor.obj X).hom.app n = X.hom.app n ≫ opObjIso.inv :=
  -- `opObjIso` is the identity isomorphism.
  (Category.comp_id _).symm

@[simp] lemma opFunctor_map_left {X Y : Augmented C} (f : X ⟶ Y) :
    (opFunctor.map f).left = f.left := (rfl)

@[simp] lemma opFunctor_map_right {X Y : Augmented C} (f : X ⟶ Y) :
    (opFunctor.map f).right = CosimplicialObject.opFunctor.map f.right := (rfl)

end Augmented

end CategoryTheory.CosimplicialObject
