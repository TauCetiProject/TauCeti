/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Op

/-!
# Reversing augmented simplicial objects

Mathlib's `SimplicialObject.opFunctor` precomposes a simplicial object with the covariant
involution `SimplexCategory.rev`, so that its `i`th face and degeneracy become the original
ones at the reversed index `i.rev`. Since `SimplexCategory.rev` fixes every object, the
augmentation of an augmented simplicial object can be kept unchanged. This gives the
reversal `SimplicialObject.Augmented.opFunctor` of augmented simplicial objects.

Mathlib's `SimplicialObject.Augmented.ExtraDegeneracy` splits the zeroth faces. After reversal,
a family of maps splitting the *last* faces, such as the one a split counit gives on a comonad
resolution, becomes such an extra degeneracy.
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.SimplicialObject.Augmented

universe v u

variable {C : Type u} [Category.{v} C]

/-- The reversal of augmented simplicial objects: precompose the simplicial part with
`SimplexCategory.rev`, keeping the augmentation object and the augmentation maps. -/
def opFunctor : Augmented C ⥤ Augmented C where
  obj X :=
    { left := SimplicialObject.opFunctor.obj X.left
      right := X.right
      hom := Functor.whiskerLeft SimplexCategory.rev.op X.hom }
  map f :=
    { left := SimplicialObject.opFunctor.map f.left
      right := f.right
      w := by
        ext n
        exact congr_app f.w (op (SimplexCategory.rev.obj n.unop)) }

@[simp] lemma opFunctor_obj_left (X : Augmented C) :
    (opFunctor.obj X).left = SimplicialObject.opFunctor.obj X.left := (rfl)

@[simp] lemma opFunctor_obj_right (X : Augmented C) :
    (opFunctor.obj X).right = X.right := (rfl)

/-- The reversed augmentation is the original augmentation. -/
@[simp] lemma opFunctor_obj_hom_app (X : Augmented C) (n : SimplexCategoryᵒᵖ) :
    (opFunctor.obj X).hom.app n = X.hom.app n := (rfl)

-- Not `simp`: `opFunctor_obj_left` already normalizes these left sides.

/-- The faces of the reversed simplicial part are the original faces at reversed indices. -/
lemma opFunctor_obj_left_δ (X : Augmented C) {n : ℕ} (i : Fin (n + 2)) :
    (opFunctor.obj X).left.δ i = X.left.δ i.rev :=
  -- `opObjIso` is the identity isomorphism.
  (SimplicialObject.opFunctor_obj_δ X.left i).trans
    ((Category.id_comp _).trans (Category.comp_id _))

/-- The degeneracies of the reversed simplicial part are the original degeneracies at reversed
indices. -/
lemma opFunctor_obj_left_σ (X : Augmented C) {n : ℕ} (i : Fin (n + 1)) :
    (opFunctor.obj X).left.σ i = X.left.σ i.rev :=
  -- `opObjIso` is the identity isomorphism.
  (SimplicialObject.opFunctor_obj_σ X.left i).trans
    ((Category.id_comp _).trans (Category.comp_id _))

@[simp] lemma opFunctor_map_left {X Y : Augmented C} (f : X ⟶ Y) :
    (opFunctor.map f).left = SimplicialObject.opFunctor.map f.left := (rfl)

@[simp] lemma opFunctor_map_right {X Y : Augmented C} (f : X ⟶ Y) :
    (opFunctor.map f).right = f.right := (rfl)

end CategoryTheory.SimplicialObject.Augmented
