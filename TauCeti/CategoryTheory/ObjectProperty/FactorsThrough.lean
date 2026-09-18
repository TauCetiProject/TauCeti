/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Factorisation
public import TauCeti.CategoryTheory.ObjectProperty

/-!
# Morphisms factoring through a class of objects

Given an object property `P` in a category, this file defines `P.FactorsThrough f`: the
morphism `f` admits a `CategoryTheory.Factorisation` whose midpoint satisfies `P`. It
records the closure properties of this predicate — enlarging `P`, composing on either side, and,
in a preadditive category, negating a factorization and adding two of them when `P` is closed
under binary products, the sum then factoring through the biproduct of the two intermediate
objects.

Everything here lives in Mathlib's root `CategoryTheory.ObjectProperty` namespace, so that
`P.FactorsThrough f` elaborates as dot notation on an object property; a copy of that namespace
nested in `TauCeti` would break it.

## Main definitions

* `CategoryTheory.ObjectProperty.FactorsThrough P f`: the morphism `f` factors through an
  object satisfying `P`.

## Main results

* `CategoryTheory.ObjectProperty.factorsThrough_iff`: the characterization of the predicate by
  an explicit intermediate object and two factors.
* `CategoryTheory.ObjectProperty.factorsThrough_id_iff`: when `P` is stable under retracts, an
  identity factors through a `P`-object exactly when its source satisfies `P`.
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

/-- A morphism factors through an object satisfying `P` if it has a factorisation whose midpoint
satisfies `P`. -/
def FactorsThrough (P : ObjectProperty C) {X Y : C} (f : X ⟶ Y) : Prop :=
  ∃ d : Factorisation f, P d.mid

/-- A morphism factors through a `P`-object if and only if it is a composite whose intermediate
object satisfies `P`. This unfolds `FactorsThrough` into an explicit intermediate object and two
factors. -/
@[simp]
theorem factorsThrough_iff (P : ObjectProperty C) {X Y : C} (f : X ⟶ Y) :
    FactorsThrough P f ↔ ∃ Q : C, P Q ∧ ∃ i : X ⟶ Q, ∃ p : Q ⟶ Y, f = i ≫ p :=
  ⟨fun ⟨d, hd⟩ ↦ ⟨d.mid, hd, d.ι, d.π, d.ι_π.symm⟩,
    fun ⟨Q, hQ, i, p, h⟩ ↦ ⟨⟨Q, i, p, h.symm⟩, hQ⟩⟩

/-- A composite through a `P`-object factors through a `P`-object. -/
theorem factorsThrough_comp (P : ObjectProperty C) {X Q Y : C} (hQ : P Q)
    (i : X ⟶ Q) (p : Q ⟶ Y) : FactorsThrough P (i ≫ p) :=
  ⟨⟨Q, i, p, rfl⟩, hQ⟩

/-- If `P` is stable under retracts, the identity of `X` factors through a `P`-object exactly
when `X` itself satisfies `P`. -/
@[simp]
theorem factorsThrough_id_iff (P : ObjectProperty C) [P.IsStableUnderRetracts] (X : C) :
    FactorsThrough P (𝟙 X) ↔ P X := by
  constructor
  · intro h
    obtain ⟨Q, hQ, i, p, h⟩ := (factorsThrough_iff P (𝟙 X)).1 h
    exact P.prop_of_retract ⟨i, p, h.symm⟩ hQ
  · intro hX
    simpa using factorsThrough_comp P hX (𝟙 X) (𝟙 X)

namespace FactorsThrough

variable {P Q : ObjectProperty C} {W X Y Z : C} {f : X ⟶ Y}

/-- Enlarging the class of intermediate objects preserves factorization. -/
theorem mono (hf : FactorsThrough P f) (hPQ : P ≤ Q) : FactorsThrough Q f := by
  obtain ⟨d, hd⟩ := hf
  exact ⟨d, hPQ _ hd⟩

/-- Precomposing preserves factorization through a `P`-object. -/
theorem comp_left (hf : FactorsThrough P f) (g : W ⟶ X) : FactorsThrough P (g ≫ f) := by
  obtain ⟨A, hA, i, p, rfl⟩ := (factorsThrough_iff P f).1 hf
  rw [← Category.assoc]
  exact factorsThrough_comp P hA (g ≫ i) p

/-- Postcomposing preserves factorization through a `P`-object. -/
theorem comp_right (hf : FactorsThrough P f) (g : Y ⟶ Z) : FactorsThrough P (f ≫ g) := by
  obtain ⟨A, hA, i, p, rfl⟩ := (factorsThrough_iff P f).1 hf
  rw [Category.assoc]
  exact factorsThrough_comp P hA i (p ≫ g)

/-- The zero morphism factors through a `P`-object when `P` is nonempty. -/
theorem zero [HasZeroMorphisms C] (P : ObjectProperty C) [P.Nonempty] (X Y : C) :
    FactorsThrough P (0 : X ⟶ Y) := by
  obtain ⟨Z, hZ⟩ := P.exists_prop_of_nonempty
  have h := factorsThrough_comp P hZ (0 : X ⟶ Z) (0 : Z ⟶ Y)
  rwa [Limits.zero_comp] at h

variable [Preadditive C]
variable {P Q : ObjectProperty C} {X Y Z : C} {f : X ⟶ Y}

/-- Negating a morphism preserves factorization through a `P`-object. -/
theorem neg (hf : FactorsThrough P f) : FactorsThrough P (-f) := by
  obtain ⟨A, hA, i, p, rfl⟩ := (factorsThrough_iff P f).1 hf
  rw [← Preadditive.neg_comp]
  exact factorsThrough_comp P hA (-i) p

/-- With binary biproducts, the sum of two factorizations through `P` factors through the
biproduct of their intermediate objects. -/
theorem add [HasBinaryBiproducts C] [P.IsClosedUnderBinaryProducts]
    {f g : X ⟶ Y} (hf : FactorsThrough P f) (hg : FactorsThrough P g) :
    FactorsThrough P (f + g) := by
  obtain ⟨A, hA, iA, pA, rfl⟩ := (factorsThrough_iff P f).1 hf
  obtain ⟨B, hB, iB, pB, rfl⟩ := (factorsThrough_iff P g).1 hg
  rw [← biprod.lift_desc]
  exact factorsThrough_comp P (P.prop_biprod_of_isClosedUnderBinaryProducts hA hB)
    (biprod.lift iA iB) (biprod.desc pA pB)

end FactorsThrough

end CategoryTheory.ObjectProperty
