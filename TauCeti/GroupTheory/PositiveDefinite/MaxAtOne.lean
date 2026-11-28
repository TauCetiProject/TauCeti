/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

import Mathlib.Tactic.Linarith

/-!
# Maximum at the identity for functions of positive type

A real function `β` on a group `G` has *positive type* if `⟪u a, u b⟫_𝕜 = β (a⁻¹ * b)` for some
family of vectors `u : G → V` in an inner product space over an `RCLike` field `𝕜`. In particular,
every vector `u a` has squared norm `β 1 ≥ 0`, `β` is symmetric under inversion (`β s⁻¹ = β s`),
and Cauchy–Schwarz gives `|β s| ≤ β 1` (hence `β s ≤ β 1`) for every `s : G`.

## Main results

* `TauCeti.apply_one_nonneg_of_inner_eq`: `0 ≤ β 1`.
* `TauCeti.apply_inv_eq_of_inner_eq`: `β s⁻¹ = β s`.
* `TauCeti.abs_le_apply_one_of_inner_eq`: `|β s| ≤ β 1`.
* `TauCeti.le_apply_one_of_inner_eq`: `β s ≤ β 1`.

## Provenance

Adapted from `grh-lean` (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), file
`src/New/Spanning/Unfolding/SquareExpansion.lean`, declaration
`New.Filling.le_apply_one_of_inner_eq`. Generalized here from `ℂ` to any `RCLike` field `𝕜`,
together with nonnegativity at `1`, inversion symmetry, and the two-sided bound `|β s| ≤ β 1`.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 G V : Type*} [RCLike 𝕜] [Group G] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- A real function `β` of positive type on a group `G` is nonnegative at `1`. -/
theorem apply_one_nonneg_of_inner_eq {β : G → ℝ} {u : G → V}
    (h : ∀ a b : G, ⟪u a, u b⟫_𝕜 = (β (a⁻¹ * b) : 𝕜)) : 0 ≤ β 1 := by
  have h_norm : ‖u 1‖ ^ 2 = β 1 := by
    rw [norm_sq_eq_re_inner (𝕜 := 𝕜), h 1 1, inv_one, one_mul, RCLike.ofReal_re]
  rw [← h_norm]
  exact sq_nonneg _

/-- A real function `β` of positive type on a group `G` is invariant under inversion:
`β s⁻¹ = β s`. -/
theorem apply_inv_eq_of_inner_eq {β : G → ℝ} {u : G → V}
    (h : ∀ a b : G, ⟪u a, u b⟫_𝕜 = (β (a⁻¹ * b) : 𝕜)) (s : G) : β s⁻¹ = β s := by
  have h1 : ⟪u s, u 1⟫_𝕜 = (β s⁻¹ : 𝕜) := by simpa using h s 1
  have h2 : ⟪u 1, u s⟫_𝕜 = (β s : 𝕜) := by simpa using h 1 s
  have hconj := inner_conj_symm (𝕜 := 𝕜) (u 1) (u s)
  rw [h1, h2, RCLike.conj_ofReal] at hconj
  exact RCLike.ofReal_injective hconj

/-- A real function `β` of positive type on a group `G` satisfies `|β s| ≤ β 1` for every `s`. -/
theorem abs_le_apply_one_of_inner_eq {β : G → ℝ} {u : G → V}
    (h : ∀ a b : G, ⟪u a, u b⟫_𝕜 = (β (a⁻¹ * b) : 𝕜)) (s : G) : |β s| ≤ β 1 := by
  have h_norm (a : G) : ‖u a‖ ^ 2 = β 1 := by
    rw [norm_sq_eq_re_inner (𝕜 := 𝕜), h a a, inv_mul_cancel, RCLike.ofReal_re]
  have h_cs : ‖⟪u 1, u s⟫_𝕜‖ ≤ ‖u 1‖ * ‖u s‖ := norm_inner_le_norm (u 1) (u s)
  have h_lhs : ‖⟪u 1, u s⟫_𝕜‖ = |β s| := by
    rw [h 1 s, inv_one, one_mul, RCLike.norm_ofReal]
  rw [h_lhs] at h_cs
  nlinarith [sq_nonneg (‖u 1‖ - ‖u s‖), h_norm 1, h_norm s]

/-- A real function `β` of positive type on a group `G` is largest at `1`: `β s ≤ β 1`. -/
theorem le_apply_one_of_inner_eq {β : G → ℝ} {u : G → V}
    (h : ∀ a b : G, ⟪u a, u b⟫_𝕜 = (β (a⁻¹ * b) : 𝕜)) (s : G) : β s ≤ β 1 :=
  (le_abs_self (β s)).trans (abs_le_apply_one_of_inner_eq h s)

end TauCeti
