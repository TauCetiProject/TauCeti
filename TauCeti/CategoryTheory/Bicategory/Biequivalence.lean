/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo

/-!
# Biequivalences of bicategories

A biequivalence between bicategories `B` and `C` consists of pseudofunctors `B ⥤ᵖ C` and
`C ⥤ᵖ B` whose two composites are equivalent to the identity pseudofunctors, as objects of the
bicategories of pseudofunctors, strong transformations and modifications. So the unit and the
counit are pseudonatural equivalences, invertible only up to invertible modifications.

## Main definitions

* `TauCeti.Biequivalence`: a biequivalence between two bicategories.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055): biequivalences.
-/

public section

namespace TauCeti

universe w₁ v₁ u₁ w₂ v₂ u₂

open CategoryTheory Bicategory Pseudofunctor.StrongTrans

/-- A biequivalence between bicategories `B` and `C`: pseudofunctors `functor : B ⥤ᵖ C` and
`inverse : C ⥤ᵖ B` with adjoint equivalences `Pseudofunctor.id B ≌ functor.comp inverse` and
`inverse.comp functor ≌ Pseudofunctor.id C` in the bicategories of pseudofunctors, strong
transformations and modifications. -/
structure Biequivalence (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂)
    [Bicategory.{w₂, v₂} C] where
  /-- The pseudofunctor from `B` to `C`. -/
  functor : B ⥤ᵖ C
  /-- The pseudofunctor from `C` to `B`. -/
  inverse : C ⥤ᵖ B
  /-- The unit: the identity of `B` is equivalent to `functor` followed by `inverse`. -/
  unitEquiv : Pseudofunctor.id B ≌ functor.comp inverse
  /-- The counit: `inverse` followed by `functor` is equivalent to the identity of `C`. -/
  counitEquiv : inverse.comp functor ≌ Pseudofunctor.id C

end TauCeti
