/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Torsor.Defs

/-!
# Basic identities for torsors

Elementary identities for a torsor `P` under a group `G` (Mathlib's `Torsor G P`) that are not
in Mathlib.

## Main results

* `TauCeti.inv_sdiv_smul`: acting on `p₁` by the inverse of `p₁ /ₛ p₂` gives `p₂`.
-/

public section

namespace TauCeti

variable {G P : Type*} [Group G] [Torsor G P]

/-- Acting on `p₁` by the inverse of `p₁ /ₛ p₂` gives `p₂`. -/
@[to_additive /-- Adding the negation of `p₁ -ᵥ p₂` to `p₁` gives `p₂`. -/]
theorem inv_sdiv_smul (p₁ p₂ : P) : (p₁ /ₛ p₂)⁻¹ • p₁ = p₂ := by
  rw [inv_sdiv_eq_sdiv_rev, sdiv_smul]

end TauCeti
