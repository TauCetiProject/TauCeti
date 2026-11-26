/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Basic

/-!
# Birkhoff sums of coboundaries

The Birkhoff sums of a coboundary `ψ ∘ T - ψ` telescope: at time `n` and point `x` they equal
`ψ (T^[n] x) - ψ x`.

## Main results

* `TauCeti.birkhoffSum_comp_sub_self_apply`: `birkhoffSum T (ψ ∘ T - ψ) n x = ψ (T^[n] x) - ψ x`.
-/

public section

namespace TauCeti

/-- The Birkhoff sums of a coboundary `ψ ∘ T - ψ` telescope: at time `n` they equal
`ψ (T^[n] x) - ψ x`. -/
@[simp]
theorem birkhoffSum_comp_sub_self_apply {X G : Type*} [AddCommGroup G] (T : X → X) (ψ : X → G)
    (n : ℕ) (x : X) :
    birkhoffSum T (ψ ∘ T - ψ) n x = ψ (T^[n] x) - ψ x := by
  rw [birkhoffSum_sub_apply, birkhoffSum_comp_apply, birkhoffSum_apply_sub_birkhoffSum]

end TauCeti
