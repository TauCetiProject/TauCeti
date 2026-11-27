/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Inner inverses and fully faithful functors

A fully faithful functor preserves and reflects whether a morphism has an inner inverse.
-/

public section

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D]

/-- The image of a morphism under a fully faithful functor has an inner inverse exactly when the
original morphism does. -/
theorem exists_comp_comp_eq_self_map_iff (F : C ⥤ D) [F.Full] [F.Faithful] {X Y : C}
    (f : X ⟶ Y) :
    (∃ g : F.obj Y ⟶ F.obj X, F.map f ≫ g ≫ F.map f = F.map f) ↔
      ∃ g : Y ⟶ X, f ≫ g ≫ f = f := by
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨g', rfl⟩ := F.map_surjective g
    exact ⟨g', F.map_injective (by simpa only [Functor.map_comp] using hg)⟩
  · rintro ⟨g, hg⟩
    exact ⟨F.map g, by simpa only [Functor.map_comp] using congrArg F.map hg⟩

end CategoryTheory.Functor
