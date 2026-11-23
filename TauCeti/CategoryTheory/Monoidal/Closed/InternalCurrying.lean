/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying

/-!
# Internal currying-uncurrying lemmas for closed monoidal categories

This file supplements `Mathlib.CategoryTheory.Monoidal.Closed.InternalCurrying` with:

* `CategoryTheory.MonoidalClosed.ihomCurryIso_hom_comp_unitNatIso_inv`: comparing
  `ihomCurryIso A (𝟙_ C) Z` with `unitNatIso.inv` recovers precomposition by `(ρ_ A).inv`;
* `CategoryTheory.MonoidalClosed.uncurry_uncurry_comp_ihomCurryIso_hom`: double uncurrying
  after `ihomCurryIso A B Z` undoes the associator and uncurries.
-/

public section

namespace CategoryTheory.MonoidalClosed

open Category MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Comparing `ihomCurryIso A (𝟙_ C) Z` with `MonoidalClosed.unitNatIso.inv` recovers precomposition
with the inverse right unitor `(ρ_ A).inv`. -/
@[reassoc]
theorem ihomCurryIso_hom_comp_unitNatIso_inv (A Z : C)
    [Closed A] [Closed (𝟙_ C)] [Closed (A ⊗ 𝟙_ C)] :
    (ihomCurryIso A (𝟙_ C) Z).hom ≫ unitNatIso.inv.app ((ihom A).obj Z) =
      (pre (ρ_ A).inv).app Z := by
  have hunitInv : unitNatIso.inv.app ((ihom A).obj Z) =
      (λ_ _).inv ≫ (ihom.ev (𝟙_ C)).app ((ihom A).obj Z) := by
    simp [unitNatIso]
  apply uncurry_injective
  rw [uncurry_pre, uncurry_eq, hunitInv,
    ← Category.assoc (ihomCurryIso A (𝟙_ C) Z).hom,
    leftUnitor_inv_naturality, Category.assoc, whiskerLeft_comp, Category.assoc,
    ← uncurry_eq, ← uncurry_eq,
    ihomCurryIso_hom, uncurry_uncurry_ihomCurry]
  simp only [Functor.id_obj]
  rw [← Category.assoc]
  congr 1
  rw [← triangle_assoc_comp_right_inv, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Double uncurrying after `ihomCurryIso A B Z` undoes the associator and uncurries. -/
theorem uncurry_uncurry_comp_ihomCurryIso_hom {A B X Z : C}
    [Closed A] [Closed B] [Closed (A ⊗ B)] (f : X ⟶ (ihom (A ⊗ B)).obj Z) :
    uncurry (uncurry (f ≫ (ihomCurryIso A B Z).hom)) = (α_ A B X).inv ≫ uncurry f := by
  rw [uncurry_natural_left, uncurry_natural_left,
    ihomCurryIso_hom, uncurry_uncurry_ihomCurry,
    associator_inv_naturality_right_assoc, ← uncurry_eq]

end CategoryTheory.MonoidalClosed
