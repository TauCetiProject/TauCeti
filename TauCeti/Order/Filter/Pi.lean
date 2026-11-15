/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Pi

/-!
# Bases for finite powers of a filter

A basis of a filter gives a basis of uniform cubes for each finite power of that filter.
-/

public section

namespace Filter.HasBasis

/-- A finite power of a filter has a basis of cubes indexed by the original basis. -/
theorem pi_self_of_finite {α κ ι : Type*} [Finite ι] {f : Filter α}
    {p : κ → Prop} {s : κ → Set α} (h : f.HasBasis p s) :
    (Filter.pi fun _ : ι ↦ f).HasBasis p (fun k ↦ Set.univ.pi fun _ ↦ s k) := by
  exact h.pi_self.to_hasBasis
    (fun k hk ↦ ⟨k.2, hk.2, fun x hx i _ ↦ hx i trivial⟩)
    (fun k hk ↦ ⟨(Set.univ, k), ⟨Set.finite_univ, hk⟩, subset_rfl⟩)

end Filter.HasBasis
