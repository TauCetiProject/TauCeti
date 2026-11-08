/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Iso

/-!
# Conjugating commutative squares along isomorphisms

Conjugating a commutative square along isomorphisms of its source and target keeps it commutative.
This holds in any category; the conjugates `i.inv ≫ f ≫ i.hom` are the underlying morphisms of
Mathlib's `CategoryTheory.Iso.conj`.

## Main results

* `CategoryTheory.comp_conj_eq_conj_comp`: conjugating a commutative square along isomorphisms of
  its source and target keeps it commutative.
-/

public section

namespace CategoryTheory

variable {C : Type*} [Category C]

/-- Conjugating a commutative square along isomorphisms keeps it commutative: if `a` and `b` are
intertwined by the composite `iX.hom ≫ d ≫ iY.inv`, then the conjugates `iX.inv ≫ a ≫ iX.hom` and
`iY.inv ≫ b ≫ iY.hom` are intertwined by `d`. -/
theorem comp_conj_eq_conj_comp {X X' Y Y' : C} (iX : X ≅ X') (iY : Y ≅ Y') (d : X' ⟶ Y')
    (a : X ⟶ X) (b : Y ⟶ Y)
    (h : (iX.hom ≫ d ≫ iY.inv) ≫ b = a ≫ iX.hom ≫ d ≫ iY.inv) :
    d ≫ (iY.inv ≫ b ≫ iY.hom) = (iX.inv ≫ a ≫ iX.hom) ≫ d := by
  rw [← cancel_epi iX.hom, ← cancel_mono iY.inv]
  simpa only [Category.assoc, Iso.hom_inv_id, Iso.hom_inv_id_assoc, Category.comp_id,
    Iso.inv_hom_id_assoc] using h

end CategoryTheory
