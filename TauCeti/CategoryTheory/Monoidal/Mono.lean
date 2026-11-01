/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Monomorphisms under monoidal whiskering

When a tensoring functor preserves monomorphisms, its whiskering notation also inherits the
corresponding `Mono` instance. These adapters let monomorphism preservation be used directly
on maps such as `X ◁ f` and `f ▷ X`, rather than only on functorial images.
-/

public section

universe v u

open CategoryTheory MonoidalCategory

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {Y Z : C}

/-- Left whiskering preserves monomorphisms when the left tensoring functor does. -/
instance mono_whiskerLeft (X : C) (f : Y ⟶ Z) [(tensorLeft X).PreservesMonomorphisms]
    [Mono f] : Mono (X ◁ f) :=
  (tensorLeft X).map_mono f

/-- Right whiskering preserves monomorphisms when the right tensoring functor does. -/
instance mono_whiskerRight (f : Y ⟶ Z) (X : C) [(tensorRight X).PreservesMonomorphisms]
    [Mono f] : Mono (f ▷ X) :=
  (tensorRight X).map_mono f

end TauCeti
