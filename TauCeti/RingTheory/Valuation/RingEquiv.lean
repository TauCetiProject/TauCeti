/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Basic

/-!
# Valuations preserved by ring isomorphisms

If a ring isomorphism preserves valuations, so does its inverse. This elementary transport
fact is independent of the topologies or completions associated with the valuations.
-/

public section

namespace Valuation

variable {K K' : Type*} [Ring K] [Ring K'] {Γ₀ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀} {w : Valuation K' Γ₀}

/-- The inverse of an isomorphism carrying `v` to `w` carries `w` to `v`. -/
theorem apply_symm_eq_of_apply_eq {σ : K ≃+* K'} (hσ : ∀ x, w (σ x) = v x) (y : K') :
    v (σ.symm y) = w y := by
  rw [← hσ, RingEquiv.apply_symm_apply]

end Valuation
