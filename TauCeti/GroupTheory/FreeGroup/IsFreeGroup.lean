/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup

/-!
# Free-group basis constructors

This file supplies computation lemmas for the free-group basis constructors from Mathlib.
-/

public section

namespace TauCeti

namespace FreeGroupBasis

universe u

/-- A basis obtained from a unique lift evaluates each generator as the supplied map. -/
@[simp] theorem ofUniqueLift_apply {G : Type u} [Group G] (X : Type u) (of : X → G)
    (h : ∀ {H : Type u} [Group H] (f : X → H), ∃! F : G →* H, ∀ a, F (of a) = f a)
    (x : X) : FreeGroupBasis.ofUniqueLift X of h x = of x := by
  change FreeGroup.lift of (FreeGroup.of x) = _
  exact FreeGroup.lift_apply_of

end FreeGroupBasis

end TauCeti
