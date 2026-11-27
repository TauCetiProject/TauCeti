/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

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

More generally over `ℝ` or `ℂ` (`RCLike 𝕜`), if an affine perturbation `x ↦ B x + b` of a
continuous linear map `B : E →L[𝕜] F` maps an open ball `Metric.ball y ρ` of positive radius `ρ`
into a bounded set `s ⊆ F`, then `‖B‖ ≤ Metric.diam s / (2 * ρ)`
(`ContinuousLinearMap.opNorm_le_diam_div_two_mul_of_mapsTo_add_ball` and its linear specialization
`ContinuousLinearMap.opNorm_le_diam_div_two_mul_of_mapsTo_ball`), and when `B` is a continuous
linear equivalence with `(B · + b) ⁻¹' w ⊆ s` and `ball z ρ ⊆ w`, the inverse satisfies
`‖(B.symm : F →L[𝕜] E)‖ ≤ Metric.diam s / (2 * ρ)`
(`ContinuousLinearEquiv.opNorm_symm_le_diam_div_two_mul_of_ball_subset`).

These bounds turn estimates of first and second derivatives in the directions of a cone into
estimates of full derivatives, and in finite-element analysis relate the derivative factors of
affine changes of variables to element diameters and inradii.

## References

* P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*, Studies in Mathematics and its
  Applications, Vol. 4, North-Holland, 1978, §3.1, Theorem 3.1.3 (ball-to-diameter bounds, stated
  there with diameters of inscribed spheres in place of radii).
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

section BallDiam

open Metric Set

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Ball-to-diameter operator-norm bound.** If `x ↦ B x + b` maps an open ball of positive
radius `ρ` into a bounded set `s`, then `‖B‖ ≤ Metric.diam s / (2 * ρ)`. -/
theorem opNorm_le_diam_div_two_mul_of_mapsTo_add_ball (B : E →L[𝕜] F) {b : F} {y : E} {ρ : ℝ}
    {s : Set F} (hρ : 0 < ρ) (hs : Bornology.IsBounded s)
    (h : MapsTo (fun x ↦ B x + b) (ball y ρ) s) :
    ‖B‖ ≤ diam s / (2 * ρ) := by
  refine B.opNorm_le_of_unit_norm (div_nonneg diam_nonneg (by positivity)) fun u hu ↦ ?_
  rcases eq_or_lt_of_le (norm_nonneg (B u)) with hBu0 | hBu
  · rw [← hBu0]
    exact div_nonneg diam_nonneg (by positivity)
  -- Test on antipodal points `y ± (t : 𝕜) • u` inside `ball y ρ` for `0 < t < ρ`.
  suffices hle : ρ ≤ diam s / (2 * ‖B u‖) by
    rw [le_div_iff₀ (by positivity)] at hle
    rw [le_div_iff₀ (by positivity)]
    linarith
  refine le_of_forall_lt_imp_le_of_dense fun t ht ↦ ?_
  rcases le_or_gt t 0 with ht0 | ht0
  · exact ht0.trans (by positivity)
  let v : E := (t : 𝕜) • u
  have hv : ‖v‖ = t := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos ht0, hu, mul_one]
  have hplus : B (y + v) + b ∈ s := h (by simpa [dist_eq_norm, hv] using ht)
  have hminus : B (y - v) + b ∈ s := h (by simpa [dist_eq_norm, hv] using ht)
  have hdist : dist (B (y + v) + b) (B (y - v) + b) ≤ diam s :=
    dist_le_diam_of_mem hs hplus hminus
  have hdiff : (B (y + v) + b) - (B (y - v) + b) = ((2 * t : ℝ) : 𝕜) • B u := by
    have hv2 : (y + v) - (y - v) = ((2 * t : ℝ) : 𝕜) • u := by
      calc (y + v) - (y - v) = v + v := by abel
        _ = ((t : 𝕜) + (t : 𝕜)) • u := (add_smul (t : 𝕜) (t : 𝕜) u).symm
        _ = ((2 * t : ℝ) : 𝕜) • u := by
          congr 1
          push_cast
          ring
    calc (B (y + v) + b) - (B (y - v) + b) = B ((y + v) - (y - v)) := by
          rw [add_sub_add_right_eq_sub, ← map_sub]
      _ = ((2 * t : ℝ) : 𝕜) • B u := by rw [hv2, map_smul]
  rw [dist_eq_norm, hdiff, norm_smul, RCLike.norm_ofReal,
    abs_of_pos (by positivity)] at hdist
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- If a continuous linear map `B` sends an open ball of positive radius `ρ` into a bounded set
`s`, then `‖B‖ ≤ Metric.diam s / (2 * ρ)`. -/
theorem opNorm_le_diam_div_two_mul_of_mapsTo_ball (B : E →L[𝕜] F) {y : E} {ρ : ℝ} {s : Set F}
    (hρ : 0 < ρ) (hs : Bornology.IsBounded s) (h : MapsTo B (ball y ρ) s) :
    ‖B‖ ≤ diam s / (2 * ρ) :=
  B.opNorm_le_diam_div_two_mul_of_mapsTo_add_ball (b := 0) hρ hs (by simpa using h)

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable {𝕜 E F : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Inverse operator-norm bound from an inscribed target ball.** If `ball z ρ ⊆ w` with `0 < ρ`
and the preimage `(fun x ↦ B x + b) ⁻¹' w` lies in a bounded set `s`, then
`‖(B.symm : F →L[𝕜] E)‖ ≤ Metric.diam s / (2 * ρ)`. -/
theorem opNorm_symm_le_diam_div_two_mul_of_ball_subset (B : E ≃L[𝕜] F) {b : F} {z : F} {ρ : ℝ}
    {s : Set E} {w : Set F} (hρ : 0 < ρ) (hs : Bornology.IsBounded s)
    (hsw : (fun x ↦ B x + b) ⁻¹' w ⊆ s) (hz : ball z ρ ⊆ w) :
    ‖(B.symm : F →L[𝕜] E)‖ ≤ diam s / (2 * ρ) := by
  refine (B.symm : F →L[𝕜] E).opNorm_le_diam_div_two_mul_of_mapsTo_add_ball
    (b := -B.symm b) (y := z) hρ hs fun y hy ↦ hsw ?_
  simp only [mem_preimage, ContinuousLinearEquiv.coe_coe, ← sub_eq_add_neg, ← map_sub,
    B.apply_symm_apply, sub_add_cancel]
  exact hz hy

end ContinuousLinearEquiv

end BallDiam
