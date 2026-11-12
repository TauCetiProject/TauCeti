/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# Binary biproducts of short complexes

Two short complexes in a category with zero morphisms have a componentwise binary direct sum,
provided the three relevant binary biproducts exist. This file constructs it and records the
projection lemmas identifying its objects and maps.

## Main definitions

* `CategoryTheory.ShortComplex.biprod`: the componentwise binary direct sum of two short
  complexes.

## Implementation notes

`ShortComplex.biprod` is `@[expose]`d so that its objects are definitionally the corresponding
biproducts outside this file. Without that, the type of `(S₁.biprod S₂).f` could not be seen to be
`S₁.X₁ ⊞ S₂.X₁ ⟶ S₁.X₂ ⊞ S₂.X₂`, and the projection lemmas for the two maps would have to be stated
with a heterogeneous equality.
-/

public section

namespace CategoryTheory.ShortComplex

open Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The componentwise binary direct sum of two short complexes. -/
@[expose, simps] noncomputable def biprod (S₁ S₂ : ShortComplex C)
    [HasBinaryBiproduct S₁.X₁ S₂.X₁] [HasBinaryBiproduct S₁.X₂ S₂.X₂]
    [HasBinaryBiproduct S₁.X₃ S₂.X₃] : ShortComplex C where
  f := biprod.map S₁.f S₂.f
  g := biprod.map S₁.g S₂.g
  zero := by ext <;> simp [reassoc_of% S₁.zero, reassoc_of% S₂.zero]

end CategoryTheory.ShortComplex
