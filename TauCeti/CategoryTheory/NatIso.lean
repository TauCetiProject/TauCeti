/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.NatIso

/-!
# Natural isomorphisms and morphism equality

A general lemma complementing Mathlib's `CategoryTheory.NatIso.naturality_1` and
`CategoryTheory.NatIso.naturality_2`: naturally isomorphic functors identify the same pairs of
parallel morphisms.

## Main results

* `CategoryTheory.NatIso.map_eq_iff`: for a natural isomorphism `e : F ≅ G`, `F.map f = F.map g`
  holds if and only if `G.map f = G.map g`.
-/

public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.NatIso

/-- Naturally isomorphic functors identify the same pairs of parallel morphisms. -/
theorem map_eq_iff {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F G : C ⥤ D} (e : F ≅ G) {X Y : C} {f g : X ⟶ Y} :
    F.map f = F.map g ↔ G.map f = G.map g :=
  ⟨fun h ↦ by rw [← NatIso.naturality_1 e, ← NatIso.naturality_1 e, h],
   fun h ↦ by rw [← NatIso.naturality_2 e, ← NatIso.naturality_2 e, h]⟩

end CategoryTheory.NatIso
