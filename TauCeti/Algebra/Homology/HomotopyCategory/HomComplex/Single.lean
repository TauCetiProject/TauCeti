/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.Restriction
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-!
# Restricted cochains into a single complex

For a cochain `α` from a cochain complex `K` indexed by `ℤ` to a single complex `Y[q]`,
`CochainComplex.HomComplex.Cochain.toSingleEquiv` reads off the component `K.X p ⟶ Y` when
`p + n = q`. When `K` is restricted along an embedding `e` of complex shapes with `e.f i = p`,
precomposing the morphism `(K.restriction e).X i ⟶ Y` of `α` with the identification
`(K.restrictionXIso e hi).inv : K.X p ≅ (K.restriction e).X i` recovers `Cochain.toSingleEquiv`
directly on `K`.

## Main results

* `CochainComplex.HomComplex.Cochain.restrictionXIso_inv_comp_toSingleEquiv`: precomposing
  `Cochain.toSingleEquiv` with `(K.restrictionXIso e hi).inv` recovers `Cochain.toSingleEquiv`
  at the target index `p`.
-/

public section

open CategoryTheory Limits HomologicalComplex CochainComplex.HomComplex

namespace CochainComplex

section Preadditive

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
  (K : CochainComplex C ℤ) (Y : C)

/-- Precomposing the morphism `(K.restriction e).X i ⟶ Y` of a cochain to `Y[q]` with the
identification `K.X p ≅ (K.restriction e).X i` gives the morphism `K.X p ⟶ Y` of the same
cochain. -/
lemma HomComplex.Cochain.restrictionXIso_inv_comp_toSingleEquiv {ι : Type*}
    {c : ComplexShape ι} (e : c.Embedding (ComplexShape.up ℤ)) [e.IsRelIff] {i : ι} {p n q : ℤ}
    (hi : e.f i = p) (h : p + n = q) (h' : e.f i + n = q)
    (α : Cochain K ((singleFunctor C q).obj Y) n) :
    (K.restrictionXIso e hi).inv ≫ Cochain.toSingleEquiv h' α =
      Cochain.toSingleEquiv h α := by
  subst hi
  -- `restrictionXIso` is defined as an `eqToIso`, which is the identity once `hi` is `rfl`
  simp [restrictionXIso]

end Preadditive

end CochainComplex
