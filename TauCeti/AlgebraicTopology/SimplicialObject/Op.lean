/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Op

/-!
# Reversing augmented simplicial objects

Mathlib's `SimplicialObject.opFunctor` reverses a simplicial object by precomposition with the
involution `SimplexCategory.rev` of the simplex category, so that its `i`-th face is the
`i.rev`-th face of the original object. Precomposition with `SimplexCategory.rev` does not change
a constant simplicial object, so the same operation reverses an augmented simplicial object
while keeping its augmentation: this is `CategoryTheory.SimplicialObject.Augmented.opFunctor`.

Mathlib's `SimplicialObject.Augmented.ExtraDegeneracy` splits the augmented object along its
zeroth faces. Reversal turns a splitting along the last faces into such an extra degeneracy.
-/

-- Exposed so that the terms of a reversed object compute to those of the original object.
@[expose] public section

open CategoryTheory Opposite

universe v u

namespace CategoryTheory.SimplicialObject.Augmented

variable {C : Type u} [Category.{v} C]

/-- Reversal of augmented simplicial objects: it reverses the simplicial part by
`SimplicialObject.opFunctor` and keeps the augmented object and the augmentation. -/
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

/-- The simplicial part of the reversed object is the reversed simplicial part. Not a `simp`
lemma: rewriting with it would turn the faces and degeneracies below into those of Mathlib's
`SimplicialObject.opFunctor`, which are stated through `SimplicialObject.opObjIso`. -/
lemma opFunctor_obj_left (X : Augmented C) :
    (opFunctor.obj X).left = _root_.SimplicialObject.opFunctor.obj X.left := (rfl)

@[simp]
lemma opFunctor_obj_right (X : Augmented C) : (opFunctor.obj X).right = X.right := (rfl)

/-- The augmentation of the reversed object is the original augmentation. -/
@[simp]
lemma opFunctor_obj_hom_app (X : Augmented C) (n : SimplexCategoryᵒᵖ) :
    (opFunctor.obj X).hom.app n = X.hom.app n := (rfl)

/-- The `i`-th face of the reversed object is the `i.rev`-th face of the original one. -/
@[simp]
lemma opFunctor_obj_left_δ (X : Augmented C) {n : ℕ} (i : Fin (n + 2)) :
    (opFunctor.obj X).left.δ i = X.left.δ i.rev := by
  simp [opFunctor, _root_.SimplicialObject.opFunctor, SimplicialObject.δ]

/-- The `i`-th degeneracy of the reversed object is the `i.rev`-th degeneracy of the original
one. -/
@[simp]
lemma opFunctor_obj_left_σ (X : Augmented C) {n : ℕ} (i : Fin (n + 1)) :
    (opFunctor.obj X).left.σ i = X.left.σ i.rev := by
  simp [opFunctor, _root_.SimplicialObject.opFunctor, SimplicialObject.σ]

@[simp]
lemma opFunctor_map_left {X Y : Augmented C} (f : X ⟶ Y) :
    (opFunctor.map f).left = _root_.SimplicialObject.opFunctor.map f.left := (rfl)

@[simp]
lemma opFunctor_map_right {X Y : Augmented C} (f : X ⟶ Y) :
    (opFunctor.map f).right = f.right := (rfl)

end CategoryTheory.SimplicialObject.Augmented
