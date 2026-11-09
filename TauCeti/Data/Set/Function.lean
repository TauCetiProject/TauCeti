/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Function

/-!
# Invariant sets of injective maps

An injective self-map fixing every point outside a set `K` maps `K` into itself.
-/

public section

open Set

namespace Function.Injective

/-- An injective map fixing every point outside `K` maps `K` into itself. -/
theorem mapsTo_of_eq_self {α : Type*} {f : α → α} (hf : Injective f) {K : Set α}
    (h : ∀ p ∉ K, f p = p) : MapsTo f K K := by
  have hs : SurjOn f Kᶜ Kᶜ := fun p hp ↦ ⟨p, hp, h p hp⟩
  simpa using hs.mapsTo_compl hf

end Function.Injective
