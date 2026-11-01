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

An adjoint equivalence `a ≌ b` in a bicategory (Mathlib's `Bicategory.Equivalence`) has an
inverse `e.symm : b ≌ a`, exchanging the two `1`-morphisms, and equivalences `a ≌ b` and
`b ≌ c` compose to `e₁.trans e₂ : a ≌ c`, with `1`-morphisms the composites. Both are built
with `Bicategory.Equivalence.mkOfAdjointifyCounit`, so only the unit and counit isomorphisms
are given and the counit is adjointified.

A biequivalence between bicategories `B` and `C` consists of pseudofunctors `B ⥤ᵖ C` and
`C ⥤ᵖ B` whose two composites are equivalent to the identity pseudofunctors, as objects of the
bicategories of pseudofunctors, strong transformations and modifications. So the unit and the
counit are pseudonatural equivalences, invertible only up to invertible modifications.

## Main definitions

* `CategoryTheory.Bicategory.Equivalence.symm`, `CategoryTheory.Bicategory.Equivalence.trans`:
  the inverse and the composite of adjoint equivalences in a bicategory;
* `CategoryTheory.Bicategory.Biequivalence`: a biequivalence between two bicategories.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055): internal adjoint equivalences in
  bicategories and biequivalences.
-/

public section

namespace CategoryTheory.Bicategory

universe w v u w₁ v₁ u₁ w₂ v₂ u₂

namespace Equivalence

variable {B : Type u} [Bicategory.{w, v} B] {a b c : B}

/-- The inverse of an adjoint equivalence in a bicategory: its `1`-morphisms are exchanged, and
its unit and counit are the inverses of the counit and the unit, adjointified. -/
def symm (e : a ≌ b) : b ≌ a :=
  mkOfAdjointifyCounit e.counit.symm e.unit.symm

@[simp]
lemma symm_hom (e : a ≌ b) : e.symm.hom = e.inv :=
  (rfl)

@[simp]
lemma symm_inv (e : a ≌ b) : e.symm.inv = e.hom :=
  (rfl)

/-- The composite of adjoint equivalences `e₁ : a ≌ b` and `e₂ : b ≌ c` in a bicategory. Its
`1`-morphisms are `e₁.hom ≫ e₂.hom` and `e₂.inv ≫ e₁.inv`; its unit inserts the unit of `e₂`
inside the unit of `e₁`, and its counit, before adjointification, inserts the counit of `e₁`
inside the counit of `e₂`. -/
def trans (e₁ : a ≌ b) (e₂ : b ≌ c) : a ≌ c :=
  mkOfAdjointifyCounit
    (e₁.unit ≪≫ whiskerLeftIso e₁.hom ((λ_ e₁.inv).symm ≪≫ whiskerRightIso e₂.unit e₁.inv ≪≫
      α_ e₂.hom e₂.inv e₁.inv) ≪≫ (α_ e₁.hom e₂.hom (e₂.inv ≫ e₁.inv)).symm)
    (α_ e₂.inv e₁.inv (e₁.hom ≫ e₂.hom) ≪≫ whiskerLeftIso e₂.inv
      ((α_ e₁.inv e₁.hom e₂.hom).symm ≪≫ whiskerRightIso e₁.counit e₂.hom ≪≫ λ_ e₂.hom) ≪≫
        e₂.counit)

@[simp]
lemma trans_hom (e₁ : a ≌ b) (e₂ : b ≌ c) : (e₁.trans e₂).hom = e₁.hom ≫ e₂.hom :=
  (rfl)

@[simp]
lemma trans_inv (e₁ : a ≌ b) (e₂ : b ≌ c) : (e₁.trans e₂).inv = e₂.inv ≫ e₁.inv :=
  (rfl)

end Equivalence

open Pseudofunctor.StrongTrans

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

end CategoryTheory.Bicategory
