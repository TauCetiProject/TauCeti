/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Biproducts of injective objects

A biproduct of injective objects is injective, for an index type in any universe. Mathlib's
instance for `⨁ c` asks for the index type to live in the universe of morphisms, which excludes
for instance the finite biproducts indexed by a `Type` in a category whose morphisms live in a
higher universe.
-/

public section

namespace TauCeti

open CategoryTheory Limits

universe w v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- A biproduct of injective objects is injective. -/
instance injective_biproduct {ι : Type w} (c : ι → C) [HasBiproduct c] [∀ i, Injective (c i)] :
    Injective (⨁ c) where
  factors g f _ := ⟨biproduct.lift fun i ↦ Injective.factorThru (g ≫ biproduct.π c i) f, by
    ext
    simp⟩

end TauCeti
