/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import TauCeti.CategoryTheory.Exact.Functor

/-!
# Exact structures with a biexact tensor product

An exact structure `E` on a monoidal additive category `C` is *monoidal* when the tensor product is
biexact: for every object `X`, tensoring on the left with `X` and tensoring on the right with `X`
carry `E`-conflations to `E`-conflations. This is the hypothesis under which the tensor product
descends to a multiplication on the exact Grothendieck group, as split short exact sequences
always do on split `K₀`.

The motivating instance is the canonical exact structure on the abelian category of
finite-dimensional representations of a monoid over a field: the tensor product over a field is
exact in each variable, while short exact sequences of representations need not split.

## Main definitions

* `TauCeti.ExactStructure.IsMonoidal`: the tensor product of `C` is biexact for `E`.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1–69, Section 5, for
  exact functors between exact categories.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe v u

namespace ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  [MonoidalCategory C] [MonoidalPreadditive C]

/-- An exact structure on a monoidal additive category is **monoidal** when its tensor product is
biexact: tensoring on either side with a fixed object is a conflation-exact functor. -/
class IsMonoidal (E : ExactStructure C) : Prop where
  /-- Tensoring on the left with a fixed object carries conflations to conflations. -/
  isConflationExact_tensorLeft (X : C) : E.IsConflationExact E (tensorLeft X)
  /-- Tensoring on the right with a fixed object carries conflations to conflations. -/
  isConflationExact_tensorRight (X : C) : E.IsConflationExact E (tensorRight X)

end ExactStructure

end TauCeti
