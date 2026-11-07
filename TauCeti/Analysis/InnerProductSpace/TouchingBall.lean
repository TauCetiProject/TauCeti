/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.LocalExtr
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Balls touching a set from inside

Facts about balls touching a set from inside, used by the classical proofs of Hopf's
boundary-point lemma and of the strong maximum principle.

Near a local maximum `x` of a function `u : E → ℝ` that is continuous near `x` but not constant
near `x`, some closed ball lies in any prescribed neighbourhood of `x`, has `u` strictly below
`u x` in its interior, and touches the level set `{u = u x}` at a point `x₀` of its sphere that
is again a local maximum. The ball is the largest one, about a point `x₂` near `x` with
`u x₂ ≠ u x`, whose interior misses the level set. A strong maximum principle follows once a
boundary-point lemma rules out such a touching ball
(`TauCeti.eventually_eq_of_isLocalMax_of_forall_not_lt_ball`).

In a real inner product space, the closed ball of radius `R / 2` that is internally tangent to
`ball y R` at `y + R • e`, for a unit vector `e`, meets the sphere `sphere y R` only at the point
of tangency (`TauCeti.mem_ball_of_mem_closedBall_half_of_ne`). So a function continuous on
`ball y R` and at `y + R • e` is continuous on that closed ball.

The barrier argument of Hopf's lemma runs on the closed annulus `closedBall y R \ ball y r`
between the touching ball and a smaller concentric ball. Its frontier lies on the two spheres
(`TauCeti.frontier_closedBall_sdiff_ball_subset`), and in a real normed space its interior is the
open annulus (`TauCeti.interior_closedBall_sdiff_ball`).

## Main declarations

* `TauCeti.eventually_eq_of_isLocalMax_of_forall_not_lt_ball`: a function continuous near a local
  maximum, which admits no touching ball as above, is constant near the maximum.
* `TauCeti.mem_ball_of_mem_closedBall_half_of_ne`: the internally tangent closed ball of half the
  radius meets the sphere only at the point of tangency.
* `TauCeti.frontier_closedBall_sdiff_ball_subset`: the frontier of a closed annulus lies on its
  two boundary spheres.
* `TauCeti.interior_closedBall_sdiff_ball`: the interior of a closed annulus is the open annulus.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  proof of Theorem 3.5.
-/

public section

namespace TauCeti

open Filter Metric Set Topology

section PseudoMetric

variable {X : Type*} [PseudoMetricSpace X]

/-- The frontier of the closed annulus `closedBall y R \ ball y r` lies on its two boundary
spheres. -/
theorem frontier_closedBall_sdiff_ball_subset (y : X) (r R : ℝ) :
    frontier (closedBall y R \ ball y r) ⊆ sphere y R ∪ sphere y r := by
  rw [sdiff_eq]
  refine (frontier_inter_subset _ _).trans (union_subset_union ?_ ?_)
  · exact inter_subset_left.trans frontier_closedBall_subset_sphere
  · rw [frontier_compl]
    exact inter_subset_right.trans frontier_ball_subset_sphere

end PseudoMetric

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- In a real normed space, the interior of the closed annulus `closedBall y R \ ball y r` with
nonzero radii is the open annulus `ball y R \ closedBall y r`. -/
theorem interior_closedBall_sdiff_ball (y : E) {r R : ℝ} (hr : r ≠ 0) (hR : R ≠ 0) :
    interior (closedBall y R \ ball y r) = ball y R \ closedBall y r := by
  rw [sdiff_eq, interior_inter, interior_compl, closure_ball y hr, interior_closedBall y hR,
    sdiff_eq]

end Seminormed

section Normed

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

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open RealInnerProductSpace

/-- The closed ball of radius `R / 2` that is internally tangent to `ball y R` at `y + R • e`
meets the sphere `sphere y R` only at the point of tangency. -/
theorem mem_ball_of_mem_closedBall_half_of_ne {y e z : E} {R : ℝ} (he : ‖e‖ = 1)
    (hz : z ∈ closedBall (y + (R / 2) • e) (R / 2)) (hne : z ≠ y + R • e) :
    z ∈ ball y R := by
  rw [mem_closedBall, dist_eq_norm] at hz
  rw [mem_ball, dist_eq_norm]
  set w := z - (y + (R / 2) • e) with hwdef
  have hR : 0 ≤ R := by linarith [norm_nonneg w]
  have hne' : w - (R / 2) • e ≠ 0 := by
    intro h
    apply hne
    rw [sub_eq_zero, hwdef, sub_eq_iff_eq_add] at h
    rw [h]
    module
  have hee : ‖(R / 2) • e‖ ^ 2 = (R / 2) ^ 2 := by
    rw [norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs]
  have h1 : ‖z - y‖ ^ 2 = ‖w‖ ^ 2 + 2 * ⟪w, (R / 2) • e⟫ + (R / 2) ^ 2 := by
    rw [show z - y = w + (R / 2) • e by rw [hwdef]; abel, norm_add_sq_real, hee]
  have h2 : ‖w - (R / 2) • e‖ ^ 2 = ‖w‖ ^ 2 - 2 * ⟪w, (R / 2) • e⟫ + (R / 2) ^ 2 := by
    rw [norm_sub_sq_real, hee]
  have h3 : 0 < ‖w - (R / 2) • e‖ ^ 2 := by positivity
  have h4 : ‖w‖ ^ 2 ≤ (R / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
  have h5 : ‖z - y‖ ^ 2 < R ^ 2 := by nlinarith
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).mp h5

end InnerProduct

end TauCeti
