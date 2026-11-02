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
Conversely, if tensor products of monomorphisms are monomorphisms, both tensoring
functors preserve monomorphisms.
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

/-- Left tensoring preserves monomorphisms if tensor products of monomorphisms are mono. -/
theorem tensorLeft_preservesMonomorphisms
    (h : ∀ {A B A' B' : C} (f : A ⟶ B) (g : A' ⟶ B') [Mono f] [Mono g], Mono (f ⊗ₘ g))
    (X : C) : (tensorLeft X).PreservesMonomorphisms where
  preserves f _ := by
    rw [curriedTensor_obj_map, ← id_tensorHom]
    exact h _ _

/-- Right tensoring preserves monomorphisms if tensor products of monomorphisms are mono. -/
theorem tensorRight_preservesMonomorphisms
    (h : ∀ {A B A' B' : C} (f : A ⟶ B) (g : A' ⟶ B') [Mono f] [Mono g], Mono (f ⊗ₘ g))
    (X : C) : (tensorRight X).PreservesMonomorphisms where
  preserves f _ := by
    rw [Functor.flip_obj_map, curriedTensor_map_app, ← tensorHom_id]
    exact h _ _

end TauCeti
