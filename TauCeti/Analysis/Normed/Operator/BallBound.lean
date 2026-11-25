/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Module.RCLike.Basic

/-!
# Operator norms from bounds on a ball

A real continuous linear map `f` bounded by `A` on a closed ball `closedBall d ρ`, about any
centre `d`, has operator norm at most `2 A / ρ`, since every vector of norm `ρ` is the difference
of two points of the ball (`ContinuousLinearMap.opNorm_le_of_forall_mem_closedBall_norm_apply_le`).

A symmetric real continuous bilinear map `B` whose quadratic map `w ↦ B w w` is bounded by `A` on
such a ball has norm at most `4 A / ρ²`
(`ContinuousLinearMap.opNorm_le_of_forall_mem_closedBall_norm_apply_self_le`). The quadratic map is
first bounded by `2 A` on the ball of radius `ρ` about `0`, through
`B z z = (B (d + z) (d + z) + B (d - z) (d - z)) / 2 - B d d`, and then `B` is bounded on pairs of
vectors by the polarization identity `4 B v w = B (v + w) (v + w) - B (v - w) (v - w)`.

These bounds turn estimates of first and second derivatives in the directions of a cone, which is
all that is available at a boundary point of a domain, into estimates of the full derivatives.
-/

public section

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- A real continuous linear map bounded by `A` on a closed ball of radius `ρ > 0`, about any
centre, has operator norm at most `2 A / ρ`: every vector of norm `ρ` is the difference of two
points of the ball. -/
theorem opNorm_le_of_forall_mem_closedBall_norm_apply_le {f : E →L[ℝ] F} {d : E} {ρ A : ℝ}
    (hρ : 0 < ρ) (hf : ∀ w ∈ Metric.closedBall d ρ, ‖f w‖ ≤ A) : ‖f‖ ≤ 2 * A / ρ := by
  have hd := hf d (Metric.mem_closedBall_self hρ.le)
  have hA : 0 ≤ A := (norm_nonneg _).trans hd
  refine opNorm_le_of_unit_norm (by positivity) fun v hv => ?_
  have hmem : d + ρ • v ∈ Metric.closedBall d ρ := by
    simp [norm_smul, hv, abs_of_pos hρ]
  have h : ρ * ‖f v‖ ≤ 2 * A := by
    calc ρ * ‖f v‖ = ‖f (d + ρ • v) - f d‖ := by
          rw [map_add, add_sub_cancel_left, map_smul, norm_smul, Real.norm_of_nonneg hρ.le]
      _ ≤ ‖f (d + ρ • v)‖ + ‖f d‖ := norm_sub_le _ _
      _ ≤ 2 * A := by linarith [hf _ hmem]
  rw [le_div_iff₀ hρ]
  linarith

/-- **Polarization bound.** A symmetric real continuous bilinear map `B` whose quadratic map
`w ↦ B w w` is bounded by `A` on a closed ball of radius `ρ > 0`, about any centre `d`, has norm at
most `4 A / ρ²`. -/
theorem opNorm_le_of_forall_mem_closedBall_norm_apply_self_le {B : E →L[ℝ] E →L[ℝ] F}
    (hB : ∀ v w, B v w = B w v) {d : E} {ρ A : ℝ} (hρ : 0 < ρ)
    (hf : ∀ w ∈ Metric.closedBall d ρ, ‖B w w‖ ≤ A) : ‖B‖ ≤ 4 * A / ρ ^ 2 := by
  have hd := hf d (Metric.mem_closedBall_self hρ.le)
  have hA : 0 ≤ A := (norm_nonneg _).trans hd
  -- The quadratic map is bounded by `2 A` on the ball of radius `ρ` about `0`.
  have h0 : ∀ z : E, ‖z‖ ≤ ρ → ‖B z z‖ ≤ 2 * A := fun z hz => by
    have hp : d + z ∈ Metric.closedBall d ρ := by simpa using hz
    have hm : d - z ∈ Metric.closedBall d ρ := by simpa using hz
    have heq : B z z = (2 : ℝ)⁻¹ • (B (d + z) (d + z) + B (d - z) (d - z)) - B d d := by
      simp only [map_add, map_sub, add_apply, sub_apply]
      module
    rw [heq]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
    linarith [norm_add_le (B (d + z) (d + z)) (B (d - z) (d - z)), hf _ hp, hf _ hm]
  -- Polarization bounds `B` on pairs of vectors of norm `c = ρ / 2`.
  refine opNorm_le_of_unit_norm (by positivity) fun v hv => opNorm_le_of_unit_norm
    (by positivity) fun w hw => ?_
  set c : ℝ := ρ / 2 with hcdef
  have hc : 0 < c := half_pos hρ
  have hpol : B (c • v) (c • w) = (4 : ℝ)⁻¹ •
      (B (c • v + c • w) (c • v + c • w) - B (c • v - c • w) (c • v - c • w)) := by
    simp only [map_add, map_sub, add_apply, sub_apply, hB (c • w) (c • v)]
    module
  have hle : ∀ z : E, ‖z‖ ≤ ‖c • v‖ + ‖c • w‖ → ‖z‖ ≤ ρ := fun z hz => by
    rw [norm_smul, norm_smul, hv, hw, Real.norm_of_nonneg hc.le] at hz
    linarith
  have hb : c * c * ‖B v w‖ ≤ A := by
    have := congrArg norm hpol
    simp only [map_smul, smul_apply, norm_smul, Real.norm_of_nonneg hc.le,
      Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4⁻¹)] at this
    have h1 := h0 _ (hle _ (norm_add_le _ _))
    have h2 := h0 _ (hle _ (norm_sub_le _ _))
    have h3 := norm_sub_le (B (c • v + c • w) (c • v + c • w)) (B (c • v - c • w) (c • v - c • w))
    nlinarith
  have hcc : c * c = ρ ^ 2 / 4 := by rw [hcdef]; ring
  rw [hcc] at hb
  rw [le_div_iff₀ (by positivity)]
  linarith

end ContinuousLinearMap
