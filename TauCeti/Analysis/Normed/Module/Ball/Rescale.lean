/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Balls under rescaling, and balls of half the norm

In a real seminormed space, the rescaling `w ↦ c + ε • w` with `ε > 0` maps the ball of radius
`r` about `0` into the ball of radius `ε r` about `c` (`TauCeti.add_smul_mem_ball`), and likewise
for closed balls with `ε ≥ 0` (`TauCeti.add_smul_mem_closedBall`).

The ball of radius `‖z - z₀‖ / 2` about a point `z ≠ z₀` stays away from `z₀` and within
`2 ‖z - z₀‖` of it (`TauCeti.ball_half_norm_sub_subset`), and the ball of radius `‖z‖ / 2` about
`z` lies outside the closed ball of radius `‖z‖ / 2` about `0`
(`TauCeti.ball_half_norm_subset`). These are the discs on which decay estimates at a puncture and
at infinity are applied.
-/

public section

open Metric Set

namespace TauCeti

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {c w : E} {ε r : ℝ}

/-- The rescaling `w ↦ c + ε • w`, `ε > 0`, maps the ball of radius `r` about `0` into the ball of
radius `ε r` about `c`. -/
theorem add_smul_mem_ball (hε : 0 < ε) (hw : w ∈ ball 0 r) : c + ε • w ∈ ball c (ε * r) := by
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hε.le]
  exact mul_lt_mul_of_pos_left (mem_ball_zero_iff.1 hw) hε

/-- The rescaling `w ↦ c + ε • w`, `ε ≥ 0`, maps the closed ball of radius `r` about `0` into the
closed ball of radius `ε r` about `c`. -/
theorem add_smul_mem_closedBall (hε : 0 ≤ ε) (hw : w ∈ closedBall 0 r) :
    c + ε • w ∈ closedBall c (ε * r) := by
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hε]
  exact mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hw) hε

end Seminormed

variable {E : Type*} [SeminormedAddCommGroup E]

/-- The ball of radius `‖z‖ / 2` about a point `z` with `‖z‖ > 2 max T 0` lies outside the closed
balls of radii `‖z‖ / 2` and `T` about `0`. -/
theorem ball_half_norm_subset {z : E} {T : ℝ} (hz : 2 * max T 0 < ‖z‖) :
    ball z (‖z‖ / 2) ⊆ (closedBall 0 (‖z‖ / 2))ᶜ ∩ (closedBall 0 T)ᶜ := by
  intro y hy
  rw [mem_ball, dist_eq_norm] at hy
  have h₁ : ‖z‖ ≤ ‖z - y‖ + ‖y‖ := by simpa using norm_add_le (z - y) y
  rw [norm_sub_rev] at h₁
  have hT := le_max_left T 0
  refine ⟨?_, ?_⟩ <;> simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] <;>
    linarith

/-- The ball of radius `‖z - z₀‖ / 2` about a point `z` of the punctured ball
`ball z₀ (R / 2) \ {z₀}` lies in the punctured ball `ball z₀ R \ {z₀}` and in the ball of radius
`2 ‖z - z₀‖` about `z₀`. -/
theorem ball_half_norm_sub_subset {E : Type*} [NormedAddCommGroup E] {z z₀ : E} {R : ℝ}
    (hz : z ∈ ball z₀ (R / 2) \ {z₀}) :
    ball z (‖z - z₀‖ / 2) ⊆ (ball z₀ R \ {z₀}) ∩ ball z₀ (2 * ‖z - z₀‖) := by
  intro y hy
  rw [mem_ball, dist_eq_norm] at hy
  have hz' : ‖z - z₀‖ < R / 2 := by simpa [dist_eq_norm] using hz.1
  have h₁ : ‖y - z₀‖ ≤ ‖y - z‖ + ‖z - z₀‖ := by simpa using norm_add_le (y - z) (z - z₀)
  have h₂ : ‖z - z₀‖ ≤ ‖z - y‖ + ‖y - z₀‖ := by simpa using norm_add_le (z - y) (y - z₀)
  rw [norm_sub_rev z y] at h₂
  have hpos : 0 < ‖z - z₀‖ := norm_pos_iff.2 (sub_ne_zero.2 hz.2)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [mem_ball, dist_eq_norm]
    linarith
  · rintro rfl
    rw [sub_self, norm_zero] at h₂
    linarith
  · rw [mem_ball, dist_eq_norm]
    linarith

end TauCeti
