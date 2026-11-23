/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Homotopy

/-!
# Naturality of homotopy inverses

A square whose horizontal sides are the forward maps of chain homotopy equivalences
`e₁ : K₁ ≃ L₁` and `e₂ : K₂ ≃ L₂` and which commutes strictly, `e₁.hom ≫ b = a ≫ e₂.hom`, gives a
square of homotopy inverses which commutes up to chain homotopy: `e₁.inv ≫ a` is homotopic to
`b ≫ e₂.inv` (`HomotopyEquiv.invNaturality`). This is how a strictly natural chain homotopy
equivalence, such as the inclusion of smooth singular chains into singular chains, has a homotopy
inverse which is natural up to chain homotopy.
-/

@[expose] public section

open CategoryTheory

namespace HomotopyEquiv

variable {C : Type*} [Category* C] [Preadditive C] {ι : Type*} {c : ComplexShape ι}
  {K₁ L₁ K₂ L₂ : HomologicalComplex C c}

/-- **Naturality up to chain homotopy of homotopy inverses.** If the forward maps of chain
homotopy equivalences `e₁` and `e₂` commute with `a` and `b`, that is `e₁.hom ≫ b = a ≫ e₂.hom`,
then `e₁.inv ≫ a` is homotopic to `b ≫ e₂.inv`. -/
def invNaturality (e₁ : HomotopyEquiv K₁ L₁) (e₂ : HomotopyEquiv K₂ L₂) {a : K₁ ⟶ K₂}
    {b : L₁ ⟶ L₂} (w : e₁.hom ≫ b = a ≫ e₂.hom) :
    Homotopy (e₁.inv ≫ a) (b ≫ e₂.inv) :=
  (Homotopy.ofEq (Category.comp_id (e₁.inv ≫ a)).symm).trans <|
    (e₂.homotopyHomInvId.symm.compLeft (e₁.inv ≫ a)).trans <|
      (Homotopy.ofEq (by
        simp only [Category.assoc]
        rw [← reassoc_of% w])).trans <|
        (e₁.homotopyInvHomId.compRight (b ≫ e₂.inv)).trans <|
          Homotopy.ofEq (Category.id_comp (b ≫ e₂.inv))

end HomotopyEquiv
