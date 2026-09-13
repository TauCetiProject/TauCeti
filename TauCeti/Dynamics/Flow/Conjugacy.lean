/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Flow

/-!
# Conjugacies of flows

This file collects general consequences of a homeomorphism that semiconjugates two flows.

## Main declarations

* `Homeomorph.map_flow_symm`: the inverse of a homeomorphic semiconjugacy satisfies the
  conjugacy equation in the reverse direction.
-/

public section

namespace Homeomorph

variable {τ α β : Type*} [TopologicalSpace τ] [TopologicalSpace α] [TopologicalSpace β]
  [AddMonoid τ] {φ : _root_.Flow τ α} {ψ : _root_.Flow τ β} (e : α ≃ₜ β)

/-- The inverse of a homeomorphic semiconjugacy is a semiconjugacy in the reverse direction. -/
theorem map_flow_symm (hconj : _root_.Flow.IsSemiconjugacy e φ ψ) (t : τ) (y : β) :
    e.symm (ψ t y) = φ t (e.symm y) := by
  apply e.injective
  rw [e.apply_symm_apply, hconj.semiconj t, e.apply_symm_apply]

end Homeomorph
