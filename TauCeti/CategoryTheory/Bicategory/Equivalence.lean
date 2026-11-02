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
equivalence. We add their composite. The unit is assembled by whiskering the two units, and
the counit is adjointified by `Bicategory.Equivalence.mkOfAdjointifyCounit`, so no triangle
identity has to be checked by hand.
-/

public section

namespace CategoryTheory.Bicategory

open Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] {a b c : B}

namespace Equivalence

/-- The composite of two equivalences in a bicategory. -/
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

end Equivalence

end CategoryTheory.Bicategory
