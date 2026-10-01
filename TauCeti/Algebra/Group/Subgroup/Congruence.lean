/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs

/-!
# Maps congruent to the identity modulo a subgroup

A map `θ : G → G` is congruent to the identity modulo a subgroup `N` when `g⁻¹ * θ g ∈ N` for
every `g`, that is when `θ g` lies in the left coset `g N` of every `g`. This file records that the
composite of two such maps is again one.

## Main results

* `TauCeti.inv_mul_apply_apply_mem`: maps congruent to the identity modulo a subgroup compose.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G]

/-- **Maps congruent to the identity modulo a subgroup compose.** If `g⁻¹ * θ g ∈ N` and
`g⁻¹ * φ g ∈ N` for every `g`, then `g⁻¹ * θ (φ g) ∈ N` for every `g`. -/
theorem inv_mul_apply_apply_mem {N : Subgroup G} {θ φ : G → G} (hθ : ∀ g, g⁻¹ * θ g ∈ N)
    (hφ : ∀ g, g⁻¹ * φ g ∈ N) (g : G) : g⁻¹ * θ (φ g) ∈ N := by
  -- `g⁻¹ * θ (φ g) = (g⁻¹ * φ g) * ((φ g)⁻¹ * θ (φ g))`.
  have := mul_mem (hφ g) (hθ (φ g))
  rwa [mul_assoc, mul_inv_cancel_left] at this

end TauCeti
