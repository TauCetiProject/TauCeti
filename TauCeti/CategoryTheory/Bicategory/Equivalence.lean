/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic

/-!
# Composition of equivalences in a bicategory

Mathlib provides adjoint equivalences `a ≌ b` in a bicategory together with the identity
equivalence. We add their composite `Bicategory.Equivalence.trans`, so that being equivalent is
a transitive relation on the objects of a bicategory, and the `1`-morphisms underlying
equivalences are closed under composition. The composite of `e : a ≌ b` and `e' : b ≌ c` has
forward `1`-morphism `e.hom ≫ e'.hom` and inverse `e'.inv ≫ e.inv`, in the reverse order.
-/

public section

namespace CategoryTheory.Bicategory

open Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b c : B}

namespace Equivalence

/-- The composite of two equivalences in a bicategory. -/
-- The unit is assembled by whiskering the two units, and the counit is adjointified by
-- `mkOfAdjointifyCounit`, so no triangle identity has to be checked by hand.
def trans (e : a ≌ b) (e' : b ≌ c) : a ≌ c :=
  mkOfAdjointifyCounit
    (e.unit ≪≫ whiskerLeftIso e.hom ((λ_ e.inv).symm ≪≫ whiskerRightIso e'.unit e.inv ≪≫
      α_ e'.hom e'.inv e.inv) ≪≫ (α_ e.hom e'.hom (e'.inv ≫ e.inv)).symm)
    (α_ e'.inv e.inv (e.hom ≫ e'.hom) ≪≫ whiskerLeftIso e'.inv ((α_ e.inv e.hom e'.hom).symm ≪≫
      whiskerRightIso e.counit e'.hom ≪≫ λ_ e'.hom) ≪≫ e'.counit)

@[simp]
lemma trans_hom (e : a ≌ b) (e' : b ≌ c) : (e.trans e').hom = e.hom ≫ e'.hom := (rfl)

@[simp]
lemma trans_inv (e : a ≌ b) (e' : b ≌ c) : (e.trans e').inv = e'.inv ≫ e.inv := (rfl)

/-- The unit of the composite equivalence whiskers the unit of `e'` into the unit of `e`. -/
@[simp]
lemma trans_unit (e : a ≌ b) (e' : b ≌ c) :
    (e.trans e').unit =
      e.unit ≪≫ whiskerLeftIso e.hom ((λ_ e.inv).symm ≪≫ whiskerRightIso e'.unit e.inv ≪≫
        α_ e'.hom e'.inv e.inv) ≪≫ (α_ e.hom e'.hom (e'.inv ≫ e.inv)).symm ≪≫
        eqToIso (congrArg₂ (· ≫ ·) (trans_hom e e') (trans_inv e e')).symm :=
  Iso.ext <| by
    simp only [Iso.trans_hom, eqToIso.hom]
    exact congrArg (e.unit.hom ≫ ·) (congrArg (_ ≫ ·) (Category.comp_id _)).symm

/-- The counit of the composite equivalence is the adjointification of the counit obtained by
whiskering the counit of `e` into the counit of `e'`. -/
@[simp]
lemma trans_counit (e : a ≌ b) (e' : b ≌ c) :
    (e.trans e').counit =
      eqToIso (congrArg₂ (· ≫ ·) (trans_inv e e') (trans_hom e e')) ≪≫
        adjointifyCounit
          (e.unit ≪≫ whiskerLeftIso e.hom ((λ_ e.inv).symm ≪≫ whiskerRightIso e'.unit e.inv ≪≫
            α_ e'.hom e'.inv e.inv) ≪≫ (α_ e.hom e'.hom (e'.inv ≫ e.inv)).symm)
          (α_ e'.inv e.inv (e.hom ≫ e'.hom) ≪≫ whiskerLeftIso e'.inv
            ((α_ e.inv e.hom e'.hom).symm ≪≫ whiskerRightIso e.counit e'.hom ≪≫ λ_ e'.hom) ≪≫
            e'.counit) :=
  Iso.ext (Category.id_comp _).symm

end Equivalence

end CategoryTheory.Bicategory
