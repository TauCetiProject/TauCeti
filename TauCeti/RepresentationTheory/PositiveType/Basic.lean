/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Gram sums over a finite group

A function `Θ` on a group `G` has *positive type* if `Θ (a⁻¹ * b) = ⟪u a, u b⟫` for vectors `u a`
of an inner product space. Pairings of this shape, depending only on `a⁻¹ * b`, have Gram sums
that collapse: if `⟪v a, w b⟫ = f (a⁻¹ * b)` for all `a, b` in a finite group `G`, then
`⟪∑ a, v a, ∑ b, w b⟫ = #G · ∑ s, f s`, since `b ↦ a⁻¹ * b` is a bijection of `G` for each `a`.

## Main results

* `TauCeti.inner_sum_sum_eq_card_mul_sum`: `⟪∑ a, v a, ∑ b, w b⟫ = #G ∑ s, f s` when
  `⟪v a, w b⟫ = f (a⁻¹ * b)`.

## References

This is adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026
Anthropic PBC), file `src/New/Spanning/SecondMoment/PositiveType.lean`
(`New.inner_sum_sum_eq_card_mul`).
-/

public section

open Finset

open scoped InnerProductSpace

namespace TauCeti

variable {G : Type*} [Group G] [Fintype G]

/-- **Gram sums over a group.** If `⟪v a, w b⟫ = f (a⁻¹ * b)` for all `a, b` in a finite group
`G`, then `⟪∑ a, v a, ∑ b, w b⟫ = #G · ∑ s, f s`. -/
theorem inner_sum_sum_eq_card_mul_sum {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {v w : G → E} (f : G → 𝕜) (h : ∀ a b, ⟪v a, w b⟫_𝕜 = f (a⁻¹ * b)) :
    ⟪∑ a, v a, ∑ b, w b⟫_𝕜 = Fintype.card G * ∑ s, f s := by
  -- For each `a` the map `b ↦ a⁻¹ * b` is a bijection of `G`.
  have h_row (a : G) : ⟪v a, ∑ b, w b⟫_𝕜 = ∑ s, f s := by
    simpa [inner_sum, h] using (Group.mulLeft_bijective a⁻¹).sum_comp f
  simp [sum_inner, h_row]

end TauCeti
