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
reversal `SimplicialObject.Augmented.opFunctor` of augmented simplicial objects. Like its
non-augmented counterpart it is an involution, so it is an equivalence
`SimplicialObject.Augmented.opEquivalence`.

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

-- Not `simp`: the lemmas below on the augmentation, on morphisms and on the involution
-- `opFunctorCompOpFunctorIso` identify morphisms of the reversed objects with morphisms of the
-- original ones only up to unfolding `opFunctor`, and as `simp` lemmas they would stop lemmas
-- about the reversed objects, such as `ExtraDegeneracy.s'_comp_ε`, from applying.

/-- The reversed augmentation is the original augmentation. -/
lemma opFunctor_obj_hom_app (X : Augmented C) (n : SimplexCategoryᵒᵖ) :
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

lemma opFunctor_map_left {X Y : Augmented C} (f : X ⟶ Y) :
    (opFunctor.map f).left = SimplicialObject.opFunctor.map f.left := (rfl)

/-- The components of a reversed morphism are the original components. -/
lemma opFunctor_map_left_app {X Y : Augmented C} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ) :
    (opFunctor.map f).left.app n = f.left.app n := (rfl)

lemma opFunctor_map_right {X Y : Augmented C} (f : X ⟶ Y) :
    (opFunctor.map f).right = f.right := (rfl)

/-- The reversal of augmented simplicial objects is an involution. -/
def opFunctorCompOpFunctorIso : opFunctor (C := C) ⋙ opFunctor ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun X ↦ Comma.isoMk (SimplicialObject.opFunctorCompOpFunctorIso.app X.left) (Iso.refl X.right)
      (by
        ext n
        rw [NatTrans.comp_app, NatTrans.comp_app, Functor.id_map, Iso.app_hom,
          SimplicialObject.opFunctorCompOpFunctorIso_hom_app_app]
        exact (Category.id_comp (𝟙 (X.left.obj n)) =≫ X.hom.app n).trans
          ((Category.id_comp (X.hom.app n)).trans (Category.comp_id (X.hom.app n)).symm)))
    (fun f ↦ hom_ext _ _ (SimplicialObject.opFunctorCompOpFunctorIso.hom.naturality f.left)
      ((Category.comp_id f.right).trans (Category.id_comp f.right).symm))

lemma opFunctorCompOpFunctorIso_hom_app_left (X : Augmented C) :
    (opFunctorCompOpFunctorIso.hom.app X).left =
      SimplicialObject.opFunctorCompOpFunctorIso.hom.app X.left := (rfl)

lemma opFunctorCompOpFunctorIso_hom_app_right (X : Augmented C) :
    (opFunctorCompOpFunctorIso.hom.app X).right = 𝟙 X.right := (rfl)

lemma opFunctorCompOpFunctorIso_inv_app_left (X : Augmented C) :
    (opFunctorCompOpFunctorIso.inv.app X).left =
      SimplicialObject.opFunctorCompOpFunctorIso.inv.app X.left := (rfl)

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
    (SimplicialObject.opEquivalence.functor_unitIso_comp X.left) (Category.id_comp _)

instance : (opFunctor (C := C)).IsEquivalence := opEquivalence.isEquivalence_functor

end CategoryTheory.SimplicialObject.Augmented
