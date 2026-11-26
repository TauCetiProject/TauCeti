/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Rev
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import TauCeti.AlgebraicTopology.SimplicialObject.Op

/-!
# Reversing cosimplicial objects

Precomposing with the covariant involution `SimplexCategory.rev` reverses a cosimplicial object:
its `i`th coface and codegeneracy become the original ones at the reversed index `i.rev`. This is
`CosimplicialObject.opFunctor`, the cosimplicial counterpart of Mathlib's
`SimplicialObject.opFunctor` (due to Joël Riou), whose conventions it follows. As there, the
terms of the reversed object are compared with the original ones through the identity
isomorphism `CosimplicialObject.opObjIso`, rather than by unfolding.

Reversal is an involution: `CosimplicialObject.opFunctorCompOpFunctorIso` identifies reversing
twice with the identity, and `CosimplicialObject.opEquivalence` is reversal as a self-equivalence.

Since `SimplexCategory.rev` fixes every object, an augmentation can be kept unchanged; this gives
the reversal `CosimplicialObject.Augmented.opFunctor` of augmented cosimplicial objects, again an
involution (`CosimplicialObject.Augmented.opFunctorCompOpFunctorIso`). Reversal commutes with
passing from an (augmented) simplicial object to the opposite (augmented) cosimplicial object
(`SimplicialObject.opFunctorObjRightOpIso`, `SimplicialObject.Augmented.opFunctorObjRightOpIso`),
so a reversed extra degeneracy can be moved to the cosimplicial side. Reversal turns a family of
maps splitting the *last* cofaces into one splitting the zeroth ones; when the reversed family,
together with a retraction of the augmentation, satisfies all the identities of an extra
codegeneracy of the reversal, that extra codegeneracy contracts the alternating coface map complex
onto the augmentation.
-/

public section

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

/-- The functor `opFunctor : CosimplicialObject C ⥤ CosimplicialObject C` is a covariant
involution. -/
def opFunctorCompOpFunctorIso : opFunctor (C := C) ⋙ opFunctor ≅ 𝟭 _ :=
  (Functor.whiskeringLeftObjCompIso _ _).symm ≪≫
    (Functor.whiskeringLeft _ _ _).mapIso SimplexCategory.revCompRevIso ≪≫
    Functor.whiskeringLeftObjIdIso

@[simp]
lemma opFunctorCompOpFunctorIso_hom_app_app (X : CosimplicialObject C) (n : SimplexCategory) :
    (opFunctorCompOpFunctorIso.hom.app X).app n = opObjIso.hom ≫ opObjIso.hom := by
  simp [opFunctorCompOpFunctorIso, opObjIso, opFunctor]

@[simp]
lemma opFunctorCompOpFunctorIso_inv_app_app (X : CosimplicialObject C) (n : SimplexCategory) :
    (opFunctorCompOpFunctorIso.inv.app X).app n = opObjIso.inv ≫ opObjIso.inv := by
  simp [opFunctorCompOpFunctorIso, opObjIso, opFunctor]

/-- The functor `opFunctor : CosimplicialObject C ⥤ CosimplicialObject C` as an equivalence of
categories. Its body is exposed because the types of its unit and counit mention its functor and
inverse, so the projection lemmas identifying them with `opFunctorCompOpFunctorIso` only typecheck
when the functor and inverse reduce to `opFunctor`. -/
@[expose, simps]
def opEquivalence : CosimplicialObject C ≌ CosimplicialObject C where
  functor := opFunctor
  inverse := opFunctor
  unitIso := opFunctorCompOpFunctorIso.symm
  counitIso := opFunctorCompOpFunctorIso

namespace Augmented

/-- The reversal of augmented cosimplicial objects: precompose the cosimplicial part with
`SimplexCategory.rev`, keeping the augmentation object and the augmentation maps. Its body is
exposed, so that the augmentation object and the cosimplicial part of a reversed object are
definitionally `X.left` and `CosimplicialObject.opFunctor.obj X.right`. -/
@[expose]
def opFunctor : Augmented C ⥤ Augmented C where
  obj X :=
    { left := X.left
      right := CosimplicialObject.opFunctor.obj X.right
      hom :=
        { app n := X.hom.app n ≫ opObjIso.inv
          naturality n m f := by
            simpa using
              congrArg (· ≫ opObjIso.inv) (X.hom.naturality (SimplexCategory.rev.map f)) } }
  map f :=
    { left := f.left
      right := CosimplicialObject.opFunctor.map f.right
      w := by
        ext n
        simpa using congrArg (· ≫ opObjIso.inv) (congr_app f.w n) }

@[simp] lemma opFunctor_obj_left (X : Augmented C) :
    (opFunctor.obj X).left = X.left := (rfl)

@[simp] lemma opFunctor_obj_right (X : Augmented C) :
    (opFunctor.obj X).right = CosimplicialObject.opFunctor.obj X.right := (rfl)

/-- The augmentation of the reversed object is the original augmentation. -/
@[simp] lemma opFunctor_obj_hom_app (X : Augmented C) (n : SimplexCategory) :
    (opFunctor.obj X).hom.app n = X.hom.app n ≫ opObjIso.inv := (rfl)

@[simp] lemma opFunctor_map_left {X Y : Augmented C} (f : X ⟶ Y) :
    (opFunctor.map f).left = f.left := (rfl)

@[simp] lemma opFunctor_map_right {X Y : Augmented C} (f : X ⟶ Y) :
    (opFunctor.map f).right = CosimplicialObject.opFunctor.map f.right := (rfl)

/-- The reversal of augmented cosimplicial objects is a covariant involution. -/
def opFunctorCompOpFunctorIso : opFunctor (C := C) ⋙ opFunctor ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun X ↦ Comma.isoMk (Iso.refl _)
      (CosimplicialObject.opFunctorCompOpFunctorIso.app X.right) (by
        ext n
        -- The square is stated for `Comma`, so `simp` cannot see its components; we restate it.
        change 𝟙 X.left ≫ X.hom.app n = ((X.hom.app n ≫ opObjIso.inv) ≫ opObjIso.inv) ≫
          (CosimplicialObject.opFunctorCompOpFunctorIso.hom.app X.right).app n
        simp [opObjIso, CosimplicialObject.opFunctor]))
    -- The components of `Comma.isoMk` are stated for `Comma`, so `simp` does not reduce them
    -- here; they are the identity and the cosimplicial double-reversal isomorphism.
    (fun f ↦ by
      ext n
      · exact (Category.comp_id _).trans (Category.id_comp _).symm
      · exact congr_app (CosimplicialObject.opFunctorCompOpFunctorIso.hom.naturality f.right) n)

@[simp]
lemma opFunctorCompOpFunctorIso_hom_app_left (X : Augmented C) :
    (opFunctorCompOpFunctorIso.hom.app X).left = 𝟙 X.left := (rfl)

@[simp]
lemma opFunctorCompOpFunctorIso_hom_app_right (X : Augmented C) :
    (opFunctorCompOpFunctorIso.hom.app X).right =
      CosimplicialObject.opFunctorCompOpFunctorIso.hom.app X.right := (rfl)

@[simp]
lemma opFunctorCompOpFunctorIso_inv_app_left (X : Augmented C) :
    (opFunctorCompOpFunctorIso.inv.app X).left = 𝟙 X.left := (rfl)

@[simp]
lemma opFunctorCompOpFunctorIso_inv_app_right (X : Augmented C) :
    (opFunctorCompOpFunctorIso.inv.app X).right =
      CosimplicialObject.opFunctorCompOpFunctorIso.inv.app X.right := (rfl)

end Augmented

end CategoryTheory.CosimplicialObject

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

open Opposite

/-- Reversing a simplicial object and then passing to the opposite cosimplicial object agrees with
passing to the opposite and then reversing. -/
def opFunctorObjRightOpIso (X : SimplicialObject C) :
    (_root_.SimplicialObject.opFunctor.obj X).rightOp ≅
      CosimplicialObject.opFunctor.obj X.rightOp :=
  NatIso.ofComponents
    (fun n ↦ (_root_.SimplicialObject.opObjIso (n := op n)).op.symm ≪≫
      (CosimplicialObject.opObjIso (X := X.rightOp) (n := n)).symm)
    (fun f ↦ by
      simp [_root_.SimplicialObject.opObjIso, CosimplicialObject.opObjIso,
        _root_.SimplicialObject.opFunctor, CosimplicialObject.opFunctor])

@[simp]
lemma opFunctorObjRightOpIso_hom_app (X : SimplicialObject C) (n : SimplexCategory) :
    X.opFunctorObjRightOpIso.hom.app n =
      (_root_.SimplicialObject.opObjIso (n := op n)).inv.op ≫ CosimplicialObject.opObjIso.inv :=
  (rfl)

@[simp]
lemma opFunctorObjRightOpIso_inv_app (X : SimplicialObject C) (n : SimplexCategory) :
    X.opFunctorObjRightOpIso.inv.app n =
      CosimplicialObject.opObjIso.hom ≫ (_root_.SimplicialObject.opObjIso (n := op n)).hom.op :=
  (rfl)

namespace Augmented

/-- Reversing an augmented simplicial object and then passing to the opposite augmented
cosimplicial object agrees with passing to the opposite and then reversing. -/
def opFunctorObjRightOpIso (X : SimplicialObject.Augmented C) :
    (opFunctor.obj X).rightOp ≅ CosimplicialObject.Augmented.opFunctor.obj X.rightOp :=
  Comma.isoMk (Iso.refl _) X.left.opFunctorObjRightOpIso
    (NatTrans.ext (funext fun n ↦ by
      -- The square is stated for `Comma`, so `simp` cannot see its components; we restate it.
      change ((CosimplicialObject.const Cᵒᵖ).map (𝟙 (op X.right))).app n ≫
          ((X.hom.app (op n)).op ≫ (CosimplicialObject.opObjIso (X := X.left.rightOp)).inv) =
        ((_root_.SimplicialObject.opFunctor.map X.hom).app (op n)).op ≫
          X.left.opFunctorObjRightOpIso.hom.app n
      simp [_root_.SimplicialObject.opObjIso, CosimplicialObject.opObjIso,
        _root_.SimplicialObject.opFunctor, CosimplicialObject.opFunctor]))

@[simp]
lemma opFunctorObjRightOpIso_hom_left (X : SimplicialObject.Augmented C) :
    X.opFunctorObjRightOpIso.hom.left = 𝟙 _ := (rfl)

@[simp]
lemma opFunctorObjRightOpIso_hom_right (X : SimplicialObject.Augmented C) :
    X.opFunctorObjRightOpIso.hom.right = X.left.opFunctorObjRightOpIso.hom := (rfl)

@[simp]
lemma opFunctorObjRightOpIso_inv_left (X : SimplicialObject.Augmented C) :
    X.opFunctorObjRightOpIso.inv.left = 𝟙 _ := (rfl)

@[simp]
lemma opFunctorObjRightOpIso_inv_right (X : SimplicialObject.Augmented C) :
    X.opFunctorObjRightOpIso.inv.right = X.left.opFunctorObjRightOpIso.inv := (rfl)

end Augmented

end CategoryTheory.SimplicialObject
