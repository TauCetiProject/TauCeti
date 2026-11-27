/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Gram sums over a finite group

A function `Θ` on a group `G` has *positive type* if `Θ (a⁻¹ * b) = ⟪u a, u b⟫` for vectors `u a`
of an inner product space. Pairings of this shape, depending only on `a⁻¹ * b`, have Gram sums
that collapse: if `⟪v a, w b⟫ = f (a⁻¹ * b)` for all `a, b` in a finite group `G`, then
`⟪∑ a, v a, ∑ b, w b⟫ = #G · ∑ s, f s`, since `b ↦ a⁻¹ * b` is a bijection of `G` for each `a`.

Such a `Θ` is positive definite in the sense of `TauCeti.GroupTheory.PositiveDefinite.Basic`,
whose kernel `(a, b) ↦ Θ (a⁻¹ * b)` is the Gram matrix of the vectors `u a`; this file works with
the vectors directly.

## Main results

* `TauCeti.inner_sum_sum_eq_card_mul_sum`: `⟪∑ a, v a, ∑ b, w b⟫ = #G ∑ s, f s` when
  `⟪v a, w b⟫ = f (a⁻¹ * b)`.
* `TauCeti.norm_sq_sum_tmul_eq_card_mul_sum`: for `Θ` of positive type, an orthonormal family `c`
  and indices `y` with `y a = y b ↔ P (a⁻¹ * b)`, `‖∑ a, c (y a) ⊗ u a‖² = #G ∑_{P s} Θ s`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit `72fead1`, Apache 2.0,
Copyright 2026 Anthropic, PBC), file `src/New/Spanning/SecondMoment/PositiveType.lean`,
declarations `New.inner_sum_sum_eq_card_mul` and `New.norm_sq_sum_tmul_eq_card_mul_sum`. Here both
results are stated over any `RCLike` field, and the tensor-norm identity is stated for any index
family `y` whose fibres are the cosets of `P`, rather than for the orbit map of a matrix
representation.
-/

public section

open Finset

open scoped InnerProductSpace TensorProduct

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

/-- **Squared norms of tensor sums against a function of positive type.** Let `Θ` have positive
type, `Θ (a⁻¹ * b) = ⟪u a, u b⟫`, let `c` be an orthonormal family and `y : G → X` a family of
indices with `y a = y b` exactly when `P (a⁻¹ * b)`. Then the squared norm of
`∑ a, c (y a) ⊗ u a` is `#G` times the `Θ`-mass of `P`. -/
theorem norm_sq_sum_tmul_eq_card_mul_sum {𝕜 X E H : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {c : X → E}
    (hc : Orthonormal 𝕜 c) (y : G → X) (P : G → Prop) [DecidablePred P]
    (hy : ∀ a b, y a = y b ↔ P (a⁻¹ * b)) {Θ : G → ℝ} {u : G → H}
    (hu : ∀ a b, ⟪u a, u b⟫_𝕜 = Θ (a⁻¹ * b)) :
    ‖∑ a, c (y a) ⊗ₜ[𝕜] u a‖ ^ 2 = Fintype.card G * ∑ s with P s, Θ s := by
  classical
  have h_inner (a b : G) : ⟪c (y a) ⊗ₜ[𝕜] u a, c (y b) ⊗ₜ[𝕜] u b⟫_𝕜 =
      ((if P (a⁻¹ * b) then Θ (a⁻¹ * b) else 0 : ℝ) : 𝕜) := by
    rw [TensorProduct.inner_tmul, orthonormal_iff_ite.1 hc, hu]
    by_cases h : P (a⁻¹ * b)
    · simp [(hy a b).2 h, h]
    · simp [mt (hy a b).1 h, h]
  rw [norm_sq_eq_re_inner (𝕜 := 𝕜), inner_sum_sum_eq_card_mul_sum
    (fun s ↦ ((if P s then Θ s else 0 : ℝ) : 𝕜)) h_inner, sum_filter]
  rw [← RCLike.ofReal_sum, ← RCLike.ofReal_natCast, ← RCLike.ofReal_mul, RCLike.ofReal_re]

end TauCeti
