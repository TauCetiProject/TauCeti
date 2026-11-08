/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category
public import TauCeti.CategoryTheory.Conj

/-!
# Conjugating tensor-compatible endomorphisms along isomorphisms

If endomorphisms `aM`, `aN`, `aMN` are compatible with a morphism `d' : M ⊗ N ⟶ P` in the sense
that `d' ≫ aMN = (aM ⊗ₘ aN) ≫ d'`, then their conjugates along isomorphisms `M ≅ M'`, `N ≅ N'`,
`P ≅ P'` are compatible with the transported morphism `d : M' ⊗ N' ⟶ P'`. Here the compatibility
of the original data is phrased through the composite
`(iM.hom ⊗ₘ iN.hom) ≫ d ≫ iMN.inv`, so that no morphism `M ⊗ N ⟶ P` need be named.

The statement is derived from the plain-category lemma `CategoryTheory.comp_conj_eq_conj_comp`
(in `TauCeti.CategoryTheory.Conj`) by taking the isomorphism `iM ⊗ᵢ iN`.

## Main results

* `CategoryTheory.MonoidalCategory.comp_conj_eq_tensorHom_conj_comp`: conjugating a
  tensor-compatible family of endomorphisms along isomorphisms of the objects keeps it
  tensor-compatible.
-/

public section

open CategoryTheory MonoidalCategory

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
