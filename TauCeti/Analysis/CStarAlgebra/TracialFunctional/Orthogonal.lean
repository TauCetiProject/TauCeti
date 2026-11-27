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

Let `τ` be a positive tracial functional on a C⋆-algebra `A` and let `p₀, p₁, …` be pairwise
star-orthogonal projections of `A` on which `τ` takes one value. For every `N`, the sum
`p₀ + ⋯ + p_{N-1}` is a projection, so it has norm at most `1`, and
`N τ(p₀) = τ(p₀ + ⋯ + p_{N-1})` is bounded by `‖τ‖`; hence `τ(p₀) = 0`
(`TauCeti.PositiveTracialFunctional.apply_eq_zero_of_pairwise_isStarOrtho`).

The values agree when the projections are Murray–von Neumann equivalent to `p₀`: if
`v_i⋆ v_i = p_i` and `v_i v_i⋆ = p₀`, then `τ(p_i) = τ(v_i⋆ v_i) = τ(v_i v_i⋆) = τ(p₀)`
(`TauCeti.PositiveTracialFunctional.apply_eq_zero_of_isMurrayVonNeumannEquivalent`). For the
compact operators and the diagonal matrix units `e_ii = e_i0 e_0i`, this is the argument that a
positive tracial functional vanishes on every `e_ii`.

## Main statements

* `TauCeti.PositiveTracialFunctional.apply_eq_zero_of_pairwise_isStarOrtho`: `τ(p₀) = 0`.
* `TauCeti.PositiveTracialFunctional.apply_eq_zero_of_isMurrayVonNeumannEquivalent`: `τ(p_i) = 0`
  for pairwise star-orthogonal projections `p_i` all equivalent to `p₀`.
-/

public section

open Function
open scoped StarRing

namespace TauCeti

namespace PositiveTracialFunctional

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : PositiveTracialFunctional A)

/-- **A positive tracial functional vanishes on an infinitely repeated projection.** If
`p₀, p₁, …` are pairwise star-orthogonal projections with `τ(p_i) = τ(p₀)` for all `i`, then
`τ(p₀) = 0`. -/
theorem apply_eq_zero_of_pairwise_isStarOrtho {p : ℕ → A} (hp : ∀ i, IsStarProjection (p i))
    (horth : Pairwise ((· ⋆⟂ ·) on p)) (heq : ∀ i, τ (p i) = τ (p 0)) : τ (p 0) = 0 := by
  set C := ‖(τ.toPositiveContinuousLinearMap : A →L[ℂ] ℂ)‖
  -- `N ‖τ(p₀)‖ = ‖τ(p₀ + ⋯ + p_{N-1})‖ ≤ C`.
  have hN (N : ℕ) : N * ‖τ (p 0)‖ ≤ C := by
    have hproj : IsStarProjection (∑ i ∈ Finset.range N, p i) :=
      IsStarProjection.sum (fun i _ ↦ hp i) fun i _ j _ hij ↦ horth hij
    have hsum : τ (∑ i ∈ Finset.range N, p i) = N * τ (p 0) := by
      simp [map_sum, heq]
    calc (N : ℝ) * ‖τ (p 0)‖ = ‖τ (∑ i ∈ Finset.range N, p i)‖ := by simp [hsum]
      _ ≤ C * ‖∑ i ∈ Finset.range N, p i‖ := τ.norm_apply_le _
      _ ≤ C * 1 := by gcongr; exact hproj.norm_le
      _ = C := mul_one C
  refine norm_eq_zero.1 (le_antisymm ?_ (norm_nonneg _))
  by_contra! h
  obtain ⟨N, hN'⟩ := exists_nat_gt (C / ‖τ (p 0)‖)
  have := hN N
  rw [div_lt_iff₀ h] at hN'
  linarith

/-- **Murray–von Neumann form.** If `p₀, p₁, …` are pairwise star-orthogonal projections and each
`p_i` is equivalent to `p₀` through `v_i` (`v_i⋆ v_i = p_i`, `v_i v_i⋆ = p₀`), then `τ(p_i) = 0` for
every `i`. -/
theorem apply_eq_zero_of_isMurrayVonNeumannEquivalent {p v : ℕ → A}
    (hp : ∀ i, IsStarProjection (p i)) (horth : Pairwise ((· ⋆⟂ ·) on p))
    (hv₁ : ∀ i, star (v i) * v i = p i) (hv₂ : ∀ i, v i * star (v i) = p 0) (i : ℕ) :
    τ (p i) = 0 := by
  have heq (i : ℕ) : τ (p i) = τ (p 0) := by
    rw [← hv₁ i, τ.map_mul_comm, hv₂ i]
  rw [heq i]
  exact τ.apply_eq_zero_of_pairwise_isStarOrtho hp horth heq

end PositiveTracialFunctional

end TauCeti
