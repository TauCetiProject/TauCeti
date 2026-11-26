/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.CategoryTheory.Exact.Biproduct
public import TauCeti.CategoryTheory.Exact.Split
public import TauCeti.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Finite direct sums of conflations

In a Quillen exact category the direct sum of a finite family of distinguished short complexes
is distinguished. The closure instance applies to any limiting fan over such a family.
`TauCeti.ExactStructure.conflation_biproduct` gives the result on the componentwise direct sum,
whose arrows are the biproduct maps of the given inflations and deflations.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), Proposition 2.9.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.ExactStructure

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  (E : ExactStructure C)

/-- Conflations are closed under finite products in the category of short complexes. -/
instance conflation_isClosedUnderFiniteProducts : E.Conflation.IsClosedUnderFiniteProducts := by
  let _ : E.Conflation.IsClosedUnderBinaryProducts :=
    E.Conflation.isClosedUnderBinaryProducts_of_exists_isLimit fun S T hS hT ↦
      ⟨_, ⟨S.isLimitBiprodFan T⟩, E.conflation_biprod hS hT⟩
  let _ : HasFiniteProducts C := hasFiniteProducts_of_has_binary_and_terminal
  let _ : HasFiniteProducts (ShortComplex C) := ⟨fun _ ↦ inferInstance⟩
  exact ObjectProperty.IsClosedUnderFiniteProducts.mk'

attribute [local instance] hasFiniteProducts_of_has_binary_and_terminal
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The componentwise direct sum of finitely many conflations is a conflation. -/
theorem conflation_biproduct {J : Type*} [Finite J] {S : J → ShortComplex C}
    (hS : ∀ j, E.Conflation (S j)) :
    E.Conflation (ShortComplex.biproduct S) :=
  E.Conflation.prop_of_isLimit_fan (ShortComplex.isBilimitBiproductBicone S).isLimit hS

/-- The direct sum of a finite family of inflations is an inflation. -/
theorem isInflation_biproduct {J : Type*} [Finite J] {X Y : J → C} {i : ∀ j, X j ⟶ Y j}
    (hi : ∀ j, E.IsInflation (i j)) : E.IsInflation (biproduct.map i) := by
  choose Z p w hS using fun j ↦ (E.isInflation_iff (i j)).mp (hi j)
  exact E.isInflation_f (E.conflation_biproduct hS)

/-- The direct sum of a finite family of deflations is a deflation. -/
theorem isDeflation_biproduct {J : Type*} [Finite J] {Y Z : J → C} {p : ∀ j, Y j ⟶ Z j}
    (hp : ∀ j, E.IsDeflation (p j)) : E.IsDeflation (biproduct.map p) := by
  choose X i w hS using fun j ↦ (E.isDeflation_iff (p j)).mp (hp j)
  exact E.isDeflation_g (E.conflation_biproduct hS)

end TauCeti.ExactStructure
