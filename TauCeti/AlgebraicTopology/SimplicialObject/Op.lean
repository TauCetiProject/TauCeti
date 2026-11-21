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
to augmented simplicial objects, keeping the augmentation object and the augmentation map. Like
its non-augmented counterpart it is an involution, so it is an equivalence
`SimplicialObject.Augmented.opEquivalence`.

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

/-- The faces of the reversed simplicial part are the original faces at reversed indices. -/
lemma opFunctor_obj_left_δ (X : Augmented C) {n : ℕ} (i : Fin (n + 2)) :
    (opFunctor.obj X).left.δ i = X.left.δ i.rev :=
  -- `opObjIso` is the identity isomorphism.
  (_root_.SimplicialObject.opFunctor_obj_δ X.left i).trans
    ((Category.id_comp _).trans (Category.comp_id _))

/-- The degeneracies of the reversed simplicial part are the original degeneracies at reversed
indices. -/
lemma opFunctor_obj_left_σ (X : Augmented C) {n : ℕ} (i : Fin (n + 1)) :
    (opFunctor.obj X).left.σ i = X.left.σ i.rev :=
  -- `opObjIso` is the identity isomorphism.
  (_root_.SimplicialObject.opFunctor_obj_σ X.left i).trans
    ((Category.id_comp _).trans (Category.comp_id _))

/-- The components of a reversed morphism are the original components. -/
lemma opFunctor_map_left_app {X Y : Augmented C} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ) :
    (opFunctor.map f).left.app n = f.left.app n := (rfl)

/-- The reversal of augmented simplicial objects is an involution. -/
def opFunctorCompOpFunctorIso : opFunctor (C := C) ⋙ opFunctor ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun X ↦ Comma.isoMk (_root_.SimplicialObject.opFunctorCompOpFunctorIso.app X.left)
      (Iso.refl X.right)
      (by
        ext n
        rw [NatTrans.comp_app, NatTrans.comp_app, Functor.id_map, Iso.app_hom,
          _root_.SimplicialObject.opFunctorCompOpFunctorIso_hom_app_app]
        exact (Category.id_comp (𝟙 (X.left.obj n)) =≫ X.hom.app n).trans
          ((Category.id_comp (X.hom.app n)).trans (Category.comp_id (X.hom.app n)).symm)))
    (fun f ↦ hom_ext _ _ (_root_.SimplicialObject.opFunctorCompOpFunctorIso.hom.naturality f.left)
      ((Category.comp_id f.right).trans (Category.id_comp f.right).symm))

lemma opFunctorCompOpFunctorIso_hom_app_left (X : Augmented C) :
    (opFunctorCompOpFunctorIso.hom.app X).left =
      _root_.SimplicialObject.opFunctorCompOpFunctorIso.hom.app X.left := (rfl)

lemma opFunctorCompOpFunctorIso_hom_app_right (X : Augmented C) :
    (opFunctorCompOpFunctorIso.hom.app X).right = 𝟙 X.right := (rfl)

lemma opFunctorCompOpFunctorIso_inv_app_left (X : Augmented C) :
    (opFunctorCompOpFunctorIso.inv.app X).left =
      _root_.SimplicialObject.opFunctorCompOpFunctorIso.inv.app X.left := (rfl)

lemma opFunctorCompOpFunctorIso_inv_app_right (X : Augmented C) :
    (opFunctorCompOpFunctorIso.inv.app X).right = 𝟙 X.right := (rfl)

/-- The reversal of augmented simplicial objects as an equivalence of categories. -/
@[simps]
def opEquivalence : Augmented C ≌ Augmented C where
  functor := opFunctor
  inverse := opFunctor
  unitIso := opFunctorCompOpFunctorIso.symm
  counitIso := opFunctorCompOpFunctorIso
  functor_unitIso_comp X := hom_ext _ _
    (by
      rw [Comma.comp_left, opFunctor_map_left, Iso.symm_hom, opFunctorCompOpFunctorIso_inv_app_left,
        opFunctorCompOpFunctorIso_hom_app_left, Comma.id_left]
      exact _root_.SimplicialObject.opEquivalence.functor_unitIso_comp X.left)
    (by
      rw [Comma.comp_right, opFunctor_map_right, Iso.symm_hom,
        opFunctorCompOpFunctorIso_inv_app_right, opFunctorCompOpFunctorIso_hom_app_right,
        Comma.id_right]
      exact Category.id_comp _)

instance : (opFunctor (C := C)).IsEquivalence := opEquivalence.isEquivalence_functor

end CategoryTheory.SimplicialObject.Augmented
