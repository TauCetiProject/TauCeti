/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying

/-!
# Unswapped internal currying in braided closed monoidal categories

Mathlib's `MonoidalClosed.ihomCurryIso` identifies `(ihom (X ⊗ Y)).obj Z` with
`(ihom Y).obj ((ihom X).obj Z)` in any closed monoidal category `C`. When `C` is braided, `β_ Y X`
restores the factor order (`CategoryTheory.MonoidalClosed.ihomTensorIso`).
-/

public section

universe v u

namespace CategoryTheory.MonoidalClosed

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]

/-- In a braided closed monoidal category, precomposing `MonoidalClosed.ihomCurryIso` with `β_ Y X`
gives the internal currying isomorphism `(ihom (X ⊗ Y)).obj Z ≅ (ihom X).obj ((ihom Y).obj Z)`. -/
noncomputable def ihomTensorIso (X Y Z : C) :
    (ihom (X ⊗ Y)).obj Z ≅ (ihom X).obj ((ihom Y).obj Z) :=
  (MonoidalClosed.internalHom.mapIso (β_ Y X).op).app Z ≪≫ ihomCurryIso Y X Z

theorem ihomTensorIso_hom (X Y Z : C) :
    (ihomTensorIso X Y Z).hom = (pre (β_ Y X).hom).app Z ≫ ihomCurry Y X Z := (rfl)
theorem ihomTensorIso_inv (X Y Z : C) :
    (ihomTensorIso X Y Z).inv = ihomUncurry Y X Z ≫ (pre (β_ Y X).inv).app Z := (rfl)

end CategoryTheory.MonoidalClosed
