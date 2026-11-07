/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Conjugating tensor-compatible endomorphisms along isomorphisms

If endomorphisms `aM`, `aN`, `aMN` are compatible with a morphism `d' : M ⊗ N ⟶ P` in the sense
that `d' ≫ aMN = (aM ⊗ₘ aN) ≫ d'`, then their conjugates along isomorphisms `M ≅ M'`, `N ≅ N'`,
`P ≅ P'` are compatible with the transported morphism `d : M' ⊗ N' ⟶ P'`. Here the compatibility
of the original data is phrased through the composite
`(iM.hom ⊗ₘ iN.hom) ≫ d ≫ iMN.inv`, so that no morphism `M ⊗ N ⟶ P` need be named.

Conjugating a commutative square along isomorphisms keeps it commutative; this holds in any
category (`CategoryTheory.comp_conj_eq_conj_comp`), and the monoidal statement follows by taking the
isomorphism `iM ⊗ᵢ iN`.

## Main results

* `CategoryTheory.comp_conj_eq_conj_comp`: conjugating a commutative square along isomorphisms of
  its source and target keeps it commutative.
* `CategoryTheory.MonoidalCategory.comp_conj_eq_tensorHom_conj_comp`: conjugating a
  tensor-compatible family of endomorphisms along isomorphisms of the objects keeps it
  tensor-compatible.
-/

public section

open CategoryTheory MonoidalCategory

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

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- Conjugating a tensor-compatible family of endomorphisms along isomorphisms of the objects
keeps it tensor-compatible: if `aM ⊗ₘ aN` and `aMN` are intertwined by the composite
`(iM.hom ⊗ₘ iN.hom) ≫ d ≫ iMN.inv`, then the conjugates `iM.inv ≫ aM ≫ iM.hom` and
`iN.inv ≫ aN ≫ iN.hom` are intertwined with `iMN.inv ≫ aMN ≫ iMN.hom` by `d`. -/
theorem comp_conj_eq_tensorHom_conj_comp {M N M' N' P P' : C} (iM : M ≅ M') (iN : N ≅ N')
    (iMN : P ≅ P') (d : M' ⊗ N' ⟶ P') (aM : M ⟶ M) (aN : N ⟶ N) (aMN : P ⟶ P)
    (hmon : (iM.hom ⊗ₘ iN.hom) ≫ d ≫ iMN.inv ≫ aMN =
      (aM ⊗ₘ aN) ≫ (iM.hom ⊗ₘ iN.hom) ≫ d ≫ iMN.inv) :
    d ≫ (iMN.inv ≫ aMN ≫ iMN.hom) =
      ((iM.inv ≫ aM ≫ iM.hom) ⊗ₘ (iN.inv ≫ aN ≫ iN.hom)) ≫ d := by
  have h := comp_conj_eq_conj_comp (iM ⊗ᵢ iN) iMN d (aM ⊗ₘ aN) aMN (by
    simpa only [tensorIso_hom, Category.assoc] using hmon)
  simpa only [tensorIso_inv, tensorIso_hom, ← tensorHom_comp_tensorHom, Category.assoc] using h

end CategoryTheory.MonoidalCategory
