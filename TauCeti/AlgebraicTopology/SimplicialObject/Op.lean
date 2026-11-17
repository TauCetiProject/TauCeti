/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Op

/-!
# Reversing augmented simplicial objects

Mathlib's `SimplicialObject.opFunctor` reverses a simplicial object along the covariant
involution `SimplexCategory.rev`, so that the face `δ i` becomes `δ i.rev`. This file extends it
to augmented simplicial objects, keeping the augmentation object and the augmentation map.

Reversal turns a contraction onto the last face into a contraction onto the first face. Since
Mathlib's `SimplicialObject.Augmented.ExtraDegeneracy` splits the zeroth face, an augmented
simplicial object whose natural extra degeneracy splits its last face is reversed before
Mathlib's contraction API applies.
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.SimplicialObject.Augmented

variable {C : Type*} [Category* C]

/-- Reverse the simplicial part of an augmented simplicial object along
`SimplexCategory.rev`, keeping the augmentation object and the augmentation map. -/
def opFunctor : Augmented C ⥤ Augmented C where
  obj X :=
    { left := _root_.SimplicialObject.opFunctor.obj X.left
      right := X.right
      hom := _root_.SimplicialObject.opFunctor.map X.hom }
  map f :=
    { left := _root_.SimplicialObject.opFunctor.map f.left
      right := f.right
      w := by
        ext n
        exact congr_app f.w (op (SimplexCategory.rev.obj n.unop)) }

@[simp] lemma opFunctor_obj_left (X : Augmented C) :
    (opFunctor.obj X).left = _root_.SimplicialObject.opFunctor.obj X.left := (rfl)

@[simp] lemma opFunctor_obj_right (X : Augmented C) :
    (opFunctor.obj X).right = X.right := (rfl)

/-- The augmentation of the reversed object is the original augmentation, through
`SimplicialObject.opObjIso`. -/
@[simp] lemma opFunctor_obj_hom_app (X : Augmented C) (n : SimplexCategoryᵒᵖ) :
    (opFunctor.obj X).hom.app n =
      _root_.SimplicialObject.opObjIso.hom ≫ X.hom.app n :=
  -- `SimplicialObject.opObjIso` is the identity.
  (Category.id_comp _).symm

@[simp] lemma opFunctor_map_left {X Y : Augmented C} (f : X ⟶ Y) :
    (opFunctor.map f).left = _root_.SimplicialObject.opFunctor.map f.left := (rfl)

@[simp] lemma opFunctor_map_right {X Y : Augmented C} (f : X ⟶ Y) :
    (opFunctor.map f).right = f.right := (rfl)

end CategoryTheory.SimplicialObject.Augmented
