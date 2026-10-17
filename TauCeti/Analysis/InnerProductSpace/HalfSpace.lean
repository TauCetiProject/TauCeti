/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Translations preserving an inner-product half-space

A translation orthogonal to the normal vector preserves a strict half-space.
-/

public section

namespace TauCeti

open scoped InnerProductSpace

/-- Every translation parallel to the boundary of the half-space `{x | c < ⟪x, ν⟫}` maps it into
itself. -/
theorem mapsTo_add_smul_of_halfSpace {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {s : Set E} {ν τ : E} {c : ℝ}
    (hΩ : ∀ x, x ∈ s ↔ c < ⟪x, ν⟫_ℝ) (hτ : ⟪τ, ν⟫_ℝ = 0) (t : ℝ) :
    Set.MapsTo (· + t • τ) s s := fun x hx => by
  have hx' := (hΩ x).1 hx
  exact (hΩ _).2 (by simpa [inner_add_left, real_inner_smul_left, hτ] using hx')

end TauCeti
