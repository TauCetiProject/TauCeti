/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EpiMono

/-!
# Additional epimorphism and monomorphism lemmas

This file records general categorical invertibility criteria derived from `Mono` and `IsSplitEpi`.
-/

public section

namespace CategoryTheory

/-- A morphism `f` is an isomorphism whenever both `f ≫ g` and `g ≫ f` are isomorphisms. -/
theorem isIso_of_isIso_comp_of_isIso_comp {C : Type*} [Category* C] {X Y : C}
    (f : X ⟶ Y) (g : Y ⟶ X) [IsIso (f ≫ g)] [IsIso (g ≫ f)] : IsIso f := by
  have : Mono f := mono_of_mono f g
  have : IsSplitEpi f := IsSplitEpi.mk'
    { section_ := inv (g ≫ f) ≫ g
      id := by simp }
  exact isIso_of_mono_of_isSplitEpi f

end CategoryTheory
