/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Balls touching a level set at a local maximum

Near a local maximum `x` of a function `u : E → ℝ` that is continuous near `x` but not constant
near `x`, some closed ball lies in any prescribed neighbourhood of `x`, has `u` strictly below
`u x` in its interior, and touches the level set `{u = u x}` at a point `x₀` of its sphere that
is again a local maximum. The ball is the largest one, about a point `x₂` near `x` with
`u x₂ ≠ u x`, whose interior misses the level set. A strong maximum principle follows once a
boundary-point lemma rules out such a touching ball
(`TauCeti.eventually_eq_of_isLocalMax_of_forall_not_lt_ball`).

## Main declarations

* `TauCeti.eventually_eq_of_isLocalMax_of_forall_not_lt_ball`: a function continuous near a local
  maximum, which admits no touching ball as above, is constant near the maximum.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  proof of Theorem 3.5.
-/

public section

namespace TauCeti

open Filter Metric Set Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- **Touching balls at a local maximum.** Let `u` be continuous near a local maximum `x`, and let
`s` be a neighbourhood of `x`. Suppose that no closed ball `closedBall y R ⊆ s` with `0 < R` has
`u < u x₀` on `ball y R` for a point `x₀ = y + R • e` of its sphere at which `u` has a local
maximum with value `u x`. Then `u` is constant near `x`. -/
theorem eventually_eq_of_isLocalMax_of_forall_not_lt_ball {u : E → ℝ} {x : E} {s : Set E}
    (hs : s ∈ 𝓝 x) (hcont : ∀ᶠ y in 𝓝 x, ContinuousAt u y) (hmax : IsLocalMax u x)
    (H : ∀ (y e : E) (R : ℝ), 0 < R → ‖e‖ = 1 → closedBall y R ⊆ s →
      IsLocalMax u (y + R • e) → u (y + R • e) = u x → ¬∀ z ∈ ball y R, u z < u (y + R • e)) :
    ∀ᶠ y in 𝓝 x, u y = u x := by
  -- Work on a ball `ball x (3 * r)` inside `s` on which `u` is continuous and bounded by `u x`.
  obtain ⟨r₀, hr₀, hr₀sub⟩ := Metric.eventually_nhds_iff_ball.mp (hcont.and (hmax.and hs))
  set r := r₀ / 3 with hr_def
  have hr : 0 < r := by positivity
  have hball : ∀ ⦃y⦄, dist y x < 3 * r → ContinuousAt u y ∧ u y ≤ u x ∧ y ∈ s := fun y hy ↦
    hr₀sub y (by rw [mem_ball]; linarith)
  by_contra hne
  -- Some point `x₂` close to `x` has a different, hence smaller, value.
  obtain ⟨x₂, hx₂x, hx₂ne⟩ : ∃ x₂, dist x₂ x < r ∧ u x₂ ≠ u x := by
    by_contra! h
    exact hne (Metric.eventually_nhds_iff.mpr ⟨r, hr, fun y hy ↦ h y hy⟩)
  -- The part `Z` of the level set `{u = u x}` in `closedBall x (2 * r)` is compact.
  set Z := closedBall x (2 * r) ∩ u ⁻¹' {u x}
  have hcontOn : ContinuousOn u (closedBall x (2 * r)) := fun y hy ↦
    (hball (by rw [mem_closedBall] at hy; linarith)).1.continuousWithinAt
  have hZclosed : IsClosed Z :=
    hcontOn.preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton
  have hZcompact : IsCompact Z :=
    (isCompact_closedBall x (2 * r)).of_isClosed_subset hZclosed inter_subset_left
  have hxZ : x ∈ Z := ⟨mem_closedBall_self (by positivity), rfl⟩
  have hx₂Z : x₂ ∉ Z := fun h ↦ hx₂ne h.2
  -- `ρ` is the distance from `x₂` to `Z`, attained at `x₀ ∈ Z`.
  set ρ := infDist x₂ Z
  have hρ : 0 < ρ := (hZclosed.notMem_iff_infDist_pos ⟨x, hxZ⟩).mp hx₂Z
  have hρr : ρ < r := (infDist_le_dist_of_mem hxZ).trans_lt hx₂x
  obtain ⟨x₀, hx₀Z, hx₀dist⟩ := hZcompact.exists_infDist_eq_dist ⟨x, hxZ⟩ x₂
  have hx₀u : u x₀ = u x := hx₀Z.2
  have hnear : ∀ ⦃y⦄, dist y x₂ ≤ ρ → dist y x < 2 * r := fun y hy ↦ by
    linarith [dist_triangle y x₂ x]
  have hlt : ∀ y ∈ ball x₂ ρ, u y < u x₀ := fun y hy ↦ by
    rw [mem_ball] at hy
    have hyx := hnear hy.le
    refine hx₀u ▸ lt_of_le_of_ne (hball (by linarith)).2.1 fun hyu ↦ ?_
    have hyZ : y ∈ Z := ⟨mem_closedBall.mpr hyx.le, hyu⟩
    have := infDist_le_dist_of_mem (x := x₂) hyZ
    rw [dist_comm] at this
    linarith
  -- Write `x₀ = x₂ + ρ • e` for the unit outward normal `e`.
  have hx₀x₂ : dist x₀ x₂ = ρ := by rw [dist_comm, ← hx₀dist]
  set e := ρ⁻¹ • (x₀ - x₂) with he_def
  have hx₀e : x₂ + ρ • e = x₀ := by
    rw [he_def, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul, add_sub_cancel]
  have he : ‖e‖ = 1 := by
    rw [he_def, norm_smul, norm_inv, Real.norm_of_nonneg hρ.le, ← dist_eq_norm, hx₀x₂,
      inv_mul_cancel₀ hρ.ne']
  -- `x₀` is again a local maximum, on the sphere of the ball touching `Z`.
  have hx₀x : dist x₀ x < 3 * r := by linarith [hnear hx₀x₂.le]
  have hx₀max : IsLocalMax u x₀ := by
    refine Metric.eventually_nhds_iff_ball.mpr ⟨3 * r - dist x₀ x, by linarith, fun y hy ↦ ?_⟩
    rw [mem_ball] at hy
    exact hx₀u ▸ (hball (by linarith [dist_triangle y x₀ x])).2.1
  have hsub : closedBall x₂ ρ ⊆ s := fun y hy ↦
    (hball (y := y) (by linarith [hnear (mem_closedBall.mp hy)])).2.2
  rw [← hx₀e] at hx₀max hx₀u hlt
  exact H x₂ e ρ hρ he hsub hx₀max hx₀u hlt

end TauCeti
