/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Orthogonal
public import TauCeti.Analysis.CStarAlgebra.TracialFunctional

/-!
# Positive tracial functionals vanish on infinitely repeated projections

Let `f` be a bounded linear map on a C⋆-ring `A` and let `p₀, p₁, …` be pairwise star-orthogonal
projections of `A` on which `f` takes one value. For every `N`, the sum `p₀ + ⋯ + p_{N-1}` is a
projection, so it has norm at most `1`, and `N ‖f(p₀)‖ = ‖f(p₀ + ⋯ + p_{N-1})‖` is bounded by
`‖f‖`; hence `f(p₀) = 0` (`ContinuousLinearMap.apply_eq_zero_of_pairwise_isStarOrtho`).

For a positive tracial functional `τ`, the values agree when the projections are
Murray–von Neumann equivalent to `p₀`: if `v_i⋆ v_i = p_i` and `v_i v_i⋆ = p₀`, then
`τ(p_i) = τ(v_i⋆ v_i) = τ(v_i v_i⋆) = τ(p₀)`
(`TauCeti.PositiveTracialFunctional.apply_eq_zero_of_star_mul_self_eq_of_mul_star_self_eq`). For
the compact operators and the diagonal matrix units `e_ii = e_i0 e_0i`, this is the argument that
a positive tracial functional vanishes on every `e_ii`.

## Main statements

* `ContinuousLinearMap.apply_eq_zero_of_pairwise_isStarOrtho`: `f(p₀) = 0`.
* `TauCeti.PositiveTracialFunctional.apply_eq_zero_of_star_mul_self_eq_of_mul_star_self_eq`:
  `τ(p_i) = 0` for pairwise star-orthogonal projections `p_i` all equivalent to `p₀`.
-/

public section

open Function
open scoped StarRing

namespace ContinuousLinearMap

variable {𝕜 A E : Type*} [RCLike 𝕜] [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
  [NormedSpace 𝕜 A] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **A bounded linear map vanishes on an infinitely repeated projection.** If `p₀, p₁, …` are
pairwise star-orthogonal projections with `f(p_i) = f(p₀)` for all `i`, then `f(p₀) = 0`. -/
theorem apply_eq_zero_of_pairwise_isStarOrtho (f : A →L[𝕜] E) {p : ℕ → A}
    (hp : ∀ i, IsStarProjection (p i)) (horth : Pairwise ((· ⋆⟂ ·) on p))
    (heq : ∀ i, f (p i) = f (p 0)) : f (p 0) = 0 := by
  -- `N ‖f(p₀)‖ = ‖f(p₀ + ⋯ + p_{N-1})‖ ≤ ‖f‖`.
  have hN (N : ℕ) : N * ‖f (p 0)‖ ≤ ‖f‖ := by
    have hproj : IsStarProjection (∑ i ∈ Finset.range N, p i) :=
      IsStarProjection.sum (fun i _ ↦ hp i) fun i _ j _ hij ↦ horth hij
    have hsum : f (∑ i ∈ Finset.range N, p i) = N • f (p 0) := by
      simp [map_sum, heq]
    calc (N : ℝ) * ‖f (p 0)‖ = ‖f (∑ i ∈ Finset.range N, p i)‖ := by
          rw [hsum, RCLike.norm_nsmul 𝕜, nsmul_eq_mul]
      _ ≤ ‖f‖ * ‖∑ i ∈ Finset.range N, p i‖ := f.le_opNorm _
      _ ≤ ‖f‖ * 1 := by gcongr; exact hproj.norm_le
      _ = ‖f‖ := mul_one _
  refine norm_eq_zero.1 (le_antisymm ?_ (norm_nonneg _))
  by_contra! h
  obtain ⟨N, hN'⟩ := exists_nat_gt (‖f‖ / ‖f (p 0)‖)
  have := hN N
  rw [div_lt_iff₀ h] at hN'
  linarith

end ContinuousLinearMap

namespace TauCeti

namespace PositiveTracialFunctional

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : PositiveTracialFunctional A)

/-- **Murray–von Neumann form.** If `p₀, p₁, …` are pairwise star-orthogonal projections and each
`p_i` is equivalent to `p₀` through `v_i` (`v_i⋆ v_i = p_i`, `v_i v_i⋆ = p₀`), then `τ(p_i) = 0` for
every `i`. -/
theorem apply_eq_zero_of_star_mul_self_eq_of_mul_star_self_eq {p v : ℕ → A}
    (hp : ∀ i, IsStarProjection (p i)) (horth : Pairwise ((· ⋆⟂ ·) on p))
    (hv₁ : ∀ i, star (v i) * v i = p i) (hv₂ : ∀ i, v i * star (v i) = p 0) (i : ℕ) :
    τ (p i) = 0 := by
  have heq (i : ℕ) : τ (p i) = τ (p 0) := by
    rw [← hv₁ i, τ.map_mul_comm, hv₂ i]
  rw [heq i]
  simpa using (τ.toPositiveContinuousLinearMap : A →L[ℂ] ℂ).apply_eq_zero_of_pairwise_isStarOrtho
    hp horth (by simpa using heq)

end PositiveTracialFunctional

end TauCeti
