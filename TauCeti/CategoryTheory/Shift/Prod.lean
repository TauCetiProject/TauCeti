/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Products.Basic

/-!
# Shifts on product categories

If two categories `C` and `D` carry shifts by the same additive monoid `A`, their product carries
the componentwise shift `(X, Y)⟦a⟧ = (X⟦a⟧, Y⟦a⟧)`, whose structure isomorphisms are taken
coordinatewise. This file constructs that shift and the commutation isomorphisms making the
projections, products of shift-compatible functors, and (when `A` is a group) the two
zero-section functors compatible with it. It is the shift underlying the pretriangulated
structure on a product of pretriangulated categories.

## Main definitions

* `TauCeti.instHasShiftProd`: the componentwise shift on `C × D`.
* `CategoryTheory.Functor.CommShift` instances for `CategoryTheory.Prod.fst C D`,
  `CategoryTheory.Prod.snd C D`, `F.prod G`, `CategoryTheory.Prod.sectL C 0` and
  `CategoryTheory.Prod.sectR 0 D`.

## Main results

* `TauCeti.shiftFunctor_prod_obj`, `TauCeti.shiftFunctor_prod_map_fst` and
  `TauCeti.shiftFunctor_prod_map_snd`: the shift acts coordinatewise on objects and morphisms.
* `TauCeti.shiftFunctorZero_prod_hom_app_fst`, `TauCeti.shiftFunctorAdd_prod_hom_app_fst` and
  their variants: the structure isomorphisms of the shift are computed coordinatewise.

## Implementation notes

The shift on `C × D` is a pair only after unfolding `CategoryTheory.hasShiftMk`, so `simp` cannot
match lemmas such as `CategoryTheory.Iso.prod_hom` against a component whose target is a shifted
object of `C × D`. The coherence proofs for the zero sections therefore close their nontrivial
coordinate by an explicit identity in the factor, to which the component is definitionally
equal.
-/

public section

namespace TauCeti

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

section HasShift

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]
  (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A]

/-- The componentwise shift on a product category: `(X, Y)⟦a⟧ = (X⟦a⟧, Y⟦a⟧)`. -/
noncomputable instance instHasShiftProd : HasShift (C × D) A :=
  hasShiftMk _ _
    { F a := (shiftFunctor C a).prod (shiftFunctor D a)
      zero := NatIso.ofComponents
        (fun X => Iso.prod ((shiftFunctorZero C A).app X.1) ((shiftFunctorZero D A).app X.2))
      add a b := NatIso.ofComponents
        (fun X => Iso.prod ((shiftFunctorAdd C a b).app X.1) ((shiftFunctorAdd D a b).app X.2))
      assoc_hom_app m₁ m₂ m₃ X := by
        apply Prod.hom_ext <;> simp [shiftFunctorAdd_assoc_hom_app, shiftFunctorAdd']
      zero_add_hom_app n X := by
        apply Prod.hom_ext <;> simp [shiftFunctorAdd_zero_add_hom_app]
      add_zero_hom_app n X := by
        apply Prod.hom_ext <;> simp [shiftFunctorAdd_add_zero_hom_app] }

variable {C D A}

/-- The shift of an object of `C × D` is the pair of the shifted coordinates. -/
@[simp]
lemma shiftFunctor_prod_obj (X : C × D) (a : A) :
    (shiftFunctor (C × D) a).obj X = ((shiftFunctor C a).obj X.1, (shiftFunctor D a).obj X.2) :=
  rfl

/-- The first coordinate of a shifted morphism of `C × D` is the shifted first coordinate. -/
@[simp]
lemma shiftFunctor_prod_map_fst {X Y : C × D} (f : X ⟶ Y) (a : A) :
    ((shiftFunctor (C × D) a).map f).1 = (shiftFunctor C a).map f.1 :=
  rfl

/-- The second coordinate of a shifted morphism of `C × D` is the shifted second coordinate. -/
@[simp]
lemma shiftFunctor_prod_map_snd {X Y : C × D} (f : X ⟶ Y) (a : A) :
    ((shiftFunctor (C × D) a).map f).2 = (shiftFunctor D a).map f.2 :=
  rfl

variable (A) in
/-- The first coordinate of `shiftFunctorZero (C × D)` is `shiftFunctorZero C`. -/
@[simp]
lemma shiftFunctorZero_prod_hom_app_fst (X : C × D) :
    ((shiftFunctorZero (C × D) A).hom.app X).1 = (shiftFunctorZero C A).hom.app X.1 :=
  rfl

variable (A) in
/-- The second coordinate of `shiftFunctorZero (C × D)` is `shiftFunctorZero D`. -/
@[simp]
lemma shiftFunctorZero_prod_hom_app_snd (X : C × D) :
    ((shiftFunctorZero (C × D) A).hom.app X).2 = (shiftFunctorZero D A).hom.app X.2 :=
  rfl

variable (A) in
/-- The first coordinate of `shiftFunctorZero (C × D)` is `shiftFunctorZero C`. -/
@[simp]
lemma shiftFunctorZero_prod_inv_app_fst (X : C × D) :
    ((shiftFunctorZero (C × D) A).inv.app X).1 = (shiftFunctorZero C A).inv.app X.1 :=
  rfl

variable (A) in
/-- The second coordinate of `shiftFunctorZero (C × D)` is `shiftFunctorZero D`. -/
@[simp]
lemma shiftFunctorZero_prod_inv_app_snd (X : C × D) :
    ((shiftFunctorZero (C × D) A).inv.app X).2 = (shiftFunctorZero D A).inv.app X.2 :=
  rfl

/-- The first coordinate of `shiftFunctorAdd (C × D)` is `shiftFunctorAdd C`. -/
@[simp]
lemma shiftFunctorAdd_prod_hom_app_fst (a b : A) (X : C × D) :
    ((shiftFunctorAdd (C × D) a b).hom.app X).1 = (shiftFunctorAdd C a b).hom.app X.1 :=
  rfl

/-- The second coordinate of `shiftFunctorAdd (C × D)` is `shiftFunctorAdd D`. -/
@[simp]
lemma shiftFunctorAdd_prod_hom_app_snd (a b : A) (X : C × D) :
    ((shiftFunctorAdd (C × D) a b).hom.app X).2 = (shiftFunctorAdd D a b).hom.app X.2 :=
  rfl

/-- The first coordinate of `shiftFunctorAdd (C × D)` is `shiftFunctorAdd C`. -/
@[simp]
lemma shiftFunctorAdd_prod_inv_app_fst (a b : A) (X : C × D) :
    ((shiftFunctorAdd (C × D) a b).inv.app X).1 = (shiftFunctorAdd C a b).inv.app X.1 :=
  rfl

/-- The second coordinate of `shiftFunctorAdd (C × D)` is `shiftFunctorAdd D`. -/
@[simp]
lemma shiftFunctorAdd_prod_inv_app_snd (a b : A) (X : C × D) :
    ((shiftFunctorAdd (C × D) a b).inv.app X).2 = (shiftFunctorAdd D a b).inv.app X.2 :=
  rfl

end HasShift

section CommShift

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A]

/-- The first projection commutes with the componentwise shift, by the identity. -/
noncomputable instance instCommShiftProdFst : (CategoryTheory.Prod.fst C D).CommShift A where
  commShiftIso a := Iso.refl _
  commShiftIso_zero := by ext; simp
  commShiftIso_add a b := by ext; simp

/-- The second projection commutes with the componentwise shift, by the identity. -/
noncomputable instance instCommShiftProdSnd : (CategoryTheory.Prod.snd C D).CommShift A where
  commShiftIso a := Iso.refl _
  commShiftIso_zero := by ext; simp
  commShiftIso_add a b := by ext; simp

/-- The commutation isomorphism of the first projection with the shift is the identity. -/
@[simp]
lemma commShiftIso_fst_hom_app (a : A) (X : C × D) :
    ((CategoryTheory.Prod.fst C D).commShiftIso a).hom.app X = 𝟙 _ :=
  rfl

/-- The inverse commutation isomorphism of the first projection with the shift is the identity. -/
@[simp]
lemma commShiftIso_fst_inv_app (a : A) (X : C × D) :
    ((CategoryTheory.Prod.fst C D).commShiftIso a).inv.app X = 𝟙 _ :=
  rfl

/-- The commutation isomorphism of the second projection with the shift is the identity. -/
@[simp]
lemma commShiftIso_snd_hom_app (a : A) (X : C × D) :
    ((CategoryTheory.Prod.snd C D).commShiftIso a).hom.app X = 𝟙 _ :=
  rfl

/-- The inverse commutation isomorphism of the second projection with the shift is the identity. -/
@[simp]
lemma commShiftIso_snd_inv_app (a : A) (X : C × D) :
    ((CategoryTheory.Prod.snd C D).commShiftIso a).inv.app X = 𝟙 _ :=
  rfl

variable {C' : Type*} [Category* C'] {D' : Type*} [Category* D'] [HasShift C' A] [HasShift D' A]
  (F : C ⥤ C') (G : D ⥤ D') [F.CommShift A] [G.CommShift A]

/-- A product of functors commuting with shifts commutes with the componentwise shifts. -/
noncomputable instance instCommShiftFunctorProd : (F.prod G).CommShift A where
  commShiftIso a := NatIso.ofComponents
    (fun X => Iso.prod ((F.commShiftIso a).app X.1) ((G.commShiftIso a).app X.2))
    (fun f => by apply Prod.hom_ext <;> simp)
  commShiftIso_zero := by ext <;> simp [Functor.commShiftIso_zero]
  commShiftIso_add a b := by ext <;> simp [Functor.commShiftIso_add]

/-- The first coordinate of the commutation isomorphism of `F.prod G` is that of `F`. -/
@[simp]
lemma commShiftIso_prod_hom_app_fst (a : A) (X : C × D) :
    (((F.prod G).commShiftIso a).hom.app X).1 = (F.commShiftIso a).hom.app X.1 :=
  rfl

/-- The first coordinate of the inverse commutation isomorphism of `F.prod G` is that of `F`. -/
@[simp]
lemma commShiftIso_prod_inv_app_fst (a : A) (X : C × D) :
    (((F.prod G).commShiftIso a).inv.app X).1 = (F.commShiftIso a).inv.app X.1 :=
  rfl

/-- The second coordinate of the commutation isomorphism of `F.prod G` is that of `G`. -/
@[simp]
lemma commShiftIso_prod_hom_app_snd (a : A) (X : C × D) :
    (((F.prod G).commShiftIso a).hom.app X).2 = (G.commShiftIso a).hom.app X.2 :=
  rfl

/-- The second coordinate of the inverse commutation isomorphism of `F.prod G` is that of `G`. -/
@[simp]
lemma commShiftIso_prod_inv_app_snd (a : A) (X : C × D) :
    (((F.prod G).commShiftIso a).inv.app X).2 = (G.commShiftIso a).inv.app X.2 :=
  rfl

end CommShift

section ZeroSection

open ZeroObject

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]
  (A : Type*) [AddGroup A] [HasShift C A] [HasShift D A]

/- In both instances below the commutation isomorphisms are pairs only up to unfolding the shift
on `C × D` (see the implementation notes), so the coordinate in the factor being inserted is
closed by an explicit identity in that factor; the other coordinate lives on zero objects. -/

/-- Inserting a zero object in the second coordinate commutes with the componentwise shift: the
commutation isomorphism is the identity in the first coordinate and the unique isomorphism
`0 ≅ 0⟦a⟧` in the second. -/
noncomputable instance instCommShiftProdSectL [HasZeroMorphisms D] [HasZeroObject D] :
    (CategoryTheory.Prod.sectL C (0 : D)).CommShift A where
  commShiftIso a := NatIso.ofComponents
    (fun X => Iso.prod (Iso.refl ((shiftFunctor C a).obj X))
      ((isZero_zero D).iso ((shiftFunctor D a).map_isZero (isZero_zero D))))
    (fun f => by
      ext
      · exact (Category.comp_id _).trans (Category.id_comp _).symm
      · exact (isZero_zero D).eq_of_src _ _)
  commShiftIso_zero := by
    ext X
    · rw [Functor.CommShift.isoZero_hom_app]
      exact ((shiftFunctorZero C A).hom_inv_id_app X).symm
    · exact (isZero_zero D).eq_of_src _ _
  commShiftIso_add a b := by
    ext X
    · rw [Functor.CommShift.isoAdd_hom_app]
      exact (by simp : (shiftFunctorAdd C a b).hom.app X ≫ 𝟙 _ ≫ (shiftFunctor C b).map (𝟙 _) ≫
        (shiftFunctorAdd C a b).inv.app X = 𝟙 _).symm
    · exact (isZero_zero D).eq_of_src _ _

/-- Inserting a zero object in the first coordinate commutes with the componentwise shift: the
commutation isomorphism is the unique isomorphism `0 ≅ 0⟦a⟧` in the first coordinate and the
identity in the second. -/
noncomputable instance instCommShiftProdSectR [HasZeroMorphisms C] [HasZeroObject C] :
    (CategoryTheory.Prod.sectR (0 : C) D).CommShift A where
  commShiftIso a := NatIso.ofComponents
    (fun X => Iso.prod ((isZero_zero C).iso ((shiftFunctor C a).map_isZero (isZero_zero C)))
      (Iso.refl ((shiftFunctor D a).obj X)))
    (fun f => by
      ext
      · exact (isZero_zero C).eq_of_src _ _
      · exact (Category.comp_id _).trans (Category.id_comp _).symm)
  commShiftIso_zero := by
    ext X
    · exact (isZero_zero C).eq_of_src _ _
    · rw [Functor.CommShift.isoZero_hom_app]
      exact ((shiftFunctorZero D A).hom_inv_id_app X).symm
  commShiftIso_add a b := by
    ext X
    · exact (isZero_zero C).eq_of_src _ _
    · rw [Functor.CommShift.isoAdd_hom_app]
      exact (by simp : (shiftFunctorAdd D a b).hom.app X ≫ 𝟙 _ ≫ (shiftFunctor D b).map (𝟙 _) ≫
        (shiftFunctorAdd D a b).inv.app X = 𝟙 _).symm

end ZeroSection

end TauCeti
