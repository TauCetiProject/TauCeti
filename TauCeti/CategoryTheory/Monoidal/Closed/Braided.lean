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
`(ihom Y).obj ((ihom X).obj Z)` whenever `X`, `Y`, and `X ⊗ Y` are closed. When the ambient
monoidal category `C` is braided and `Y ⊗ X` is also closed, precomposing with the braiding
`β_ Y X` restores the factor order (`CategoryTheory.MonoidalClosed.ihomTensorIso`).
-/

public section

universe v u

namespace CategoryTheory.MonoidalClosed

open Category MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- In a braided monoidal category, precomposing `MonoidalClosed.ihomCurryIso Y X Z` with the
braiding `β_ Y X` gives the internal currying isomorphism
`(ihom (X ⊗ Y)).obj Z ≅ (ihom X).obj ((ihom Y).obj Z)`. -/
noncomputable def ihomTensorIso (X Y Z : C) [Closed X] [Closed Y] [Closed (X ⊗ Y)]
    [Closed (Y ⊗ X)] :
    (ihom (X ⊗ Y)).obj Z ≅ (ihom X).obj ((ihom Y).obj Z) where
  hom := (pre (β_ Y X).hom).app Z ≫ ihomCurry Y X Z
  inv := ihomUncurry Y X Z ≫ (pre (β_ Y X).inv).app Z
  hom_inv_id := by
    rw [Category.assoc, ihomCurry_ihomUncurry_assoc, ← NatTrans.comp_app, ← pre_map,
      Iso.inv_hom_id, pre_id, NatTrans.id_app]
  inv_hom_id := by
    rw [Category.assoc, ← Category.assoc (pre (β_ Y X).inv |>.app Z), ← NatTrans.comp_app,
      ← pre_map, Iso.hom_inv_id, pre_id, NatTrans.id_app, Category.id_comp,
      ihomUncurry_ihomCurry]

theorem ihomTensorIso_hom (X Y Z : C) [Closed X] [Closed Y] [Closed (X ⊗ Y)] [Closed (Y ⊗ X)] :
    (ihomTensorIso X Y Z).hom = (pre (β_ Y X).hom).app Z ≫ ihomCurry Y X Z := (rfl)

theorem ihomTensorIso_inv (X Y Z : C) [Closed X] [Closed Y] [Closed (X ⊗ Y)] [Closed (Y ⊗ X)] :
    (ihomTensorIso X Y Z).inv = ihomUncurry Y X Z ≫ (pre (β_ Y X).inv).app Z := (rfl)

end CategoryTheory.MonoidalClosed
