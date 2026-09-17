/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.ObjectProperty

/-!
# Morphisms factoring through a class of objects

Given an object property `P` in a category, this file defines `P.FactorsThrough f`: the morphism
`f` is a composite whose intermediate object satisfies `P`. It records the closure properties of
this predicate — enlarging `P`, composing on either side, and, in a preadditive category, negating
a factorization and adding two of them when `P` is closed under binary products, the sum then
factoring through the biproduct of the two intermediate objects.

Everything here lives in Mathlib's root `CategoryTheory.ObjectProperty` namespace, so that
`P.FactorsThrough f` elaborates as dot notation on an object property; a copy of that namespace
nested in `TauCeti` would break it.

## Main definitions

* `CategoryTheory.ObjectProperty.FactorsThrough P f`: the morphism `f` factors through an
  object satisfying `P`.

## Main results

* `CategoryTheory.ObjectProperty.factorsThrough_iff`: the characterization of the predicate by
  its defining existential statement, through which consumers of this file obtain the
  intermediate object and the two factors.
* `CategoryTheory.ObjectProperty.FactorsThrough.add`: over a preadditive category with binary
  biproducts, a sum of factorizations through a product-closed `P` again factors through a
  single `P`-object.

## References

* M. Auslander, I. Reiten, S. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  Studies in Advanced Mathematics 36, CUP (1995), Chapter IV, Section 1.
-/

public section

universe v u

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type u} [Category.{v} C]

/-- A morphism factors through an object satisfying `P` if it is a composite whose intermediate
object satisfies `P`. -/
def FactorsThrough (P : ObjectProperty C) {X Y : C} (f : X ⟶ Y) : Prop :=
  ∃ Q : C, P Q ∧ ∃ i : X ⟶ Q, ∃ p : Q ⟶ Y, f = i ≫ p

/-- A morphism factors through a `P`-object if and only if it is a composite whose intermediate
object satisfies `P`. This is the elimination principle for `FactorsThrough`, whose body is not
exposed to importing modules. -/
theorem factorsThrough_iff (P : ObjectProperty C) {X Y : C} (f : X ⟶ Y) :
    FactorsThrough P f ↔ ∃ Q : C, P Q ∧ ∃ i : X ⟶ Q, ∃ p : Q ⟶ Y, f = i ≫ p :=
  Iff.rfl

/-- A composite through a `P`-object factors through a `P`-object. -/
theorem factorsThrough_comp (P : ObjectProperty C) {X Q Y : C} (hQ : P Q)
    (i : X ⟶ Q) (p : Q ⟶ Y) : FactorsThrough P (i ≫ p) :=
  ⟨Q, hQ, i, p, rfl⟩

namespace FactorsThrough

variable {P Q : ObjectProperty C} {W X Y Z : C} {f : X ⟶ Y}

/-- Enlarging the class of intermediate objects preserves factorization. -/
theorem mono (hf : FactorsThrough P f) (hPQ : P ≤ Q) : FactorsThrough Q f := by
  obtain ⟨A, hA, i, p, rfl⟩ := hf
  exact ⟨A, hPQ _ hA, i, p, rfl⟩

/-- Precomposing preserves factorization through a `P`-object. -/
theorem comp_left (hf : FactorsThrough P f) (g : W ⟶ X) : FactorsThrough P (g ≫ f) := by
  obtain ⟨A, hA, i, p, rfl⟩ := hf
  exact ⟨A, hA, g ≫ i, p, (Category.assoc _ _ _).symm⟩

/-- Postcomposing preserves factorization through a `P`-object. -/
theorem comp_right (hf : FactorsThrough P f) (g : Y ⟶ Z) : FactorsThrough P (f ≫ g) := by
  obtain ⟨A, hA, i, p, rfl⟩ := hf
  exact ⟨A, hA, i, p ≫ g, Category.assoc _ _ _⟩

/-- The zero morphism factors through a `P`-object when `P` is nonempty. -/
theorem zero [HasZeroMorphisms C] (P : ObjectProperty C) [P.Nonempty] (X Y : C) :
    FactorsThrough P (0 : X ⟶ Y) := by
  obtain ⟨Z, hZ⟩ := P.exists_prop_of_nonempty
  exact ⟨Z, hZ, 0, 0, Limits.zero_comp.symm⟩

variable [Preadditive C]
variable {P Q : ObjectProperty C} {X Y Z : C} {f : X ⟶ Y}

/-- Negating a morphism preserves factorization through a `P`-object. -/
theorem neg (hf : FactorsThrough P f) : FactorsThrough P (-f) := by
  obtain ⟨A, hA, i, p, rfl⟩ := hf
  exact ⟨A, hA, -i, p, (Preadditive.neg_comp _ _).symm⟩

/-- With binary biproducts, the sum of two factorizations through `P` factors through the
biproduct of their intermediate objects. -/
theorem add [HasBinaryBiproducts C] [P.IsClosedUnderBinaryProducts]
    {f g : X ⟶ Y} (hf : FactorsThrough P f) (hg : FactorsThrough P g) :
    FactorsThrough P (f + g) := by
  obtain ⟨A, hA, iA, pA, rfl⟩ := hf
  obtain ⟨B, hB, iB, pB, rfl⟩ := hg
  exact ⟨A ⊞ B, P.prop_biprod_of_isClosedUnderBinaryProducts hA hB,
    biprod.lift iA iB, biprod.desc pA pB, biprod.lift_desc.symm⟩

end FactorsThrough

end CategoryTheory.ObjectProperty
