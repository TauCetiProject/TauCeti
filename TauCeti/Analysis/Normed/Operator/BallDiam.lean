/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Bounding operator norms from inscribed balls and image diameters

If an affine perturbation `x ↦ B x + b` of a continuous linear map `B : E →L[𝕜] F` over `ℝ` or `ℂ`
maps an open ball `Metric.ball y ρ` of positive radius `ρ` into a bounded set `s ⊆ F`, then

`‖B‖ ≤ Metric.diam s / (2 * ρ)`.

Indeed, for any nonzero vector `u` and `0 < t < ρ`, the antipodal points `y ± (t / ‖u‖) • u` lie in
`Metric.ball y ρ`, so their affine images lie in `s` at distance `(2 * t / ‖u‖) * ‖B u‖ ≤ diam s`;
letting `t` approach `ρ` yields the operator-norm estimate. When `B` is a continuous linear
equivalence and `s = (fun x ↦ B x + b) ⁻¹' w`, applying the same argument to the inverse affine map
`z ↦ B.symm z - B.symm b` bounds `‖B.symm‖` in terms of `Metric.diam s` and the radius of any ball
inscribed in `w`.

In finite-element analysis this geometric estimate relates the derivative factors in affine changes
of variables between a reference element and a physical element to their diameters and inradii.

## Main declarations

* `ContinuousLinearMap.opNorm_le_diam_div_two_mul_of_mapsTo_add_ball`: `‖B‖ ≤ diam s / (2 * ρ)`
  when `x ↦ B x + b` maps `ball y ρ` into a bounded set `s`.
* `ContinuousLinearMap.opNorm_le_diam_div_two_mul_of_mapsTo_ball`: the linear specialization
  (`b = 0`).
* `ContinuousLinearMap.opNorm_le_diam_div_two_mul_of_ball_subset_preimage_add`: preimage-inclusion
  form of the bound.
* `ContinuousLinearEquiv.opNorm_symm_le_diam_div_two_mul_of_ball_subset`: the dual bound
  `‖(B.symm : F →L[𝕜] E)‖ ≤ diam s / (2 * ρ)` when `ball z ρ ⊆ w` and `(B · + b) ⁻¹' w ⊆ s`.

## References

* P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*, Studies in Mathematics and its
  Applications, Vol. 4, North-Holland, 1978, §3.1, Theorem 3.1.3 (stated there with diameters of
  inscribed spheres in place of radii).
-/

public section

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
  refine B.opNorm_le_bound (div_nonneg diam_nonneg (by positivity)) fun u ↦ ?_
  rcases eq_or_lt_of_le (norm_nonneg u) with hu0 | hu
  · rw [← hu0, mul_zero]
    exact by simpa [← hu0] using B.le_opNorm u
  rcases eq_or_lt_of_le (norm_nonneg (B u)) with hBu0 | hBu
  · rw [← hBu0]
    exact mul_nonneg (div_nonneg diam_nonneg (by positivity)) hu.le
  -- Test on antipodal points `y ± (t / ‖u‖) • u` inside `ball y ρ` for `0 < t < ρ`.
  suffices hle : ρ ≤ diam s * ‖u‖ / (2 * ‖B u‖) by
    rw [le_div_iff₀ (by positivity)] at hle
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  refine le_of_forall_lt_imp_le_of_dense fun t ht ↦ ?_
  rcases le_or_gt t 0 with ht0 | ht0
  · exact ht0.trans (by positivity)
  let c : 𝕜 := (t / ‖u‖ : ℝ)
  let v : E := c • u
  have hv : ‖v‖ = t := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (div_pos ht0 hu), div_mul_cancel₀ _ hu.ne']
  have hplus : B (y + v) + b ∈ s := h (by simpa [dist_eq_norm, hv] using ht)
  have hminus : B (y - v) + b ∈ s := h (by simpa [dist_eq_norm, hv] using ht)
  have hdist : dist (B (y + v) + b) (B (y - v) + b) ≤ diam s :=
    dist_le_diam_of_mem hs hplus hminus
  have hdiff : (B (y + v) + b) - (B (y - v) + b) = ((2 * t / ‖u‖ : ℝ) : 𝕜) • B u := by
    have hv2 : (y + v) - (y - v) = ((2 * t / ‖u‖ : ℝ) : 𝕜) • u := by
      calc (y + v) - (y - v) = v + v := by abel
        _ = (c + c) • u := (add_smul c c u).symm
        _ = ((2 * t / ‖u‖ : ℝ) : 𝕜) • u := by
          congr 1
          dsimp only [c]
          push_cast
          ring
    calc (B (y + v) + b) - (B (y - v) + b) = B ((y + v) - (y - v)) := by
          rw [add_sub_add_right_eq_sub, ← map_sub]
      _ = ((2 * t / ‖u‖ : ℝ) : 𝕜) • B u := by rw [hv2, map_smul]
  rw [dist_eq_norm, hdiff, norm_smul, RCLike.norm_ofReal,
    abs_of_pos (by positivity)] at hdist
  rw [le_div_iff₀ (by positivity)]
  have hmul := mul_le_mul_of_nonneg_right hdist hu.le
  have hsimp : 2 * t / ‖u‖ * ‖B u‖ * ‖u‖ = t * (2 * ‖B u‖) := by
    field_simp
  linarith

/-- If a continuous linear map `B` sends an open ball of positive radius `ρ` into a bounded set
`s`, then `‖B‖ ≤ Metric.diam s / (2 * ρ)`. -/
theorem opNorm_le_diam_div_two_mul_of_mapsTo_ball (B : E →L[𝕜] F) {y : E} {ρ : ℝ} {s : Set F}
    (hρ : 0 < ρ) (hs : Bornology.IsBounded s) (h : MapsTo B (ball y ρ) s) :
    ‖B‖ ≤ diam s / (2 * ρ) :=
  B.opNorm_le_diam_div_two_mul_of_mapsTo_add_ball (b := 0) hρ hs (by simpa using h)

/-- Preimage-inclusion form of `ContinuousLinearMap.opNorm_le_diam_div_two_mul_of_mapsTo_add_ball`:
if `ball y ρ` lies in the preimage of a bounded set `s` under `x ↦ B x + b`, then
`‖B‖ ≤ Metric.diam s / (2 * ρ)`. -/
theorem opNorm_le_diam_div_two_mul_of_ball_subset_preimage_add (B : E →L[𝕜] F) {b : F} {y : E}
    {ρ : ℝ} {s : Set F} (hρ : 0 < ρ) (hs : Bornology.IsBounded s)
    (h : ball y ρ ⊆ (fun x ↦ B x + b) ⁻¹' s) :
    ‖B‖ ≤ diam s / (2 * ρ) :=
  B.opNorm_le_diam_div_two_mul_of_mapsTo_add_ball hρ hs (mapsTo_iff_subset_preimage.2 h)

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

/-- Specialization of `ContinuousLinearEquiv.opNorm_symm_le_diam_div_two_mul_of_ball_subset` when
`s = (fun x ↦ B x + b) ⁻¹' w`. -/
theorem opNorm_symm_le_diam_div_two_mul_of_eq_preimage (B : E ≃L[𝕜] F) {b : F} {z : F} {ρ : ℝ}
    {s : Set E} {w : Set F} (hρ : 0 < ρ) (hs : Bornology.IsBounded s)
    (hsw : s = (fun x ↦ B x + b) ⁻¹' w) (hz : ball z ρ ⊆ w) :
    ‖(B.symm : F →L[𝕜] E)‖ ≤ diam s / (2 * ρ) :=
  B.opNorm_symm_le_diam_div_two_mul_of_ball_subset hρ hs hsw.symm.subset hz

end ContinuousLinearEquiv
