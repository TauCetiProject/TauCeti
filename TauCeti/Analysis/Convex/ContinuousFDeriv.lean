/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Convex.Function
import TauCeti.Analysis.Convex.Strong

/-!
# Differentiable convex functions are continuously differentiable

A real convex function on a neighbourhood of a point `x` of a real normed space, differentiable at
every point near `x`, has a derivative that is continuous at `x`
(`ConvexOn.continuousAt_fderiv`). So a convex function differentiable on an open set is `C¹`
there (`ConvexOn.continuousOn_fderiv`). No finite dimensionality is needed.

The proof is quantitative. The derivative `L'` at a point `x'` is a subgradient of the convex
function `g`, so `L' (t • h) ≤ g (x' + t • h) - g x'`. If `x'` is within `r / 3` of `x`, and `g`
is within `η ‖z - x‖` of its first-order expansion `g x + L (z - x)` on the ball of radius `r`
about `x`, the step `t • h` of length `r / 3` gives `(L' - L) h ≤ 3 η ‖h‖`, and the same for
`-h`.

## Main results

* `TauCeti.apply_sub_apply_le_of_forall_add_le`: a subgradient at a point near a
  point of differentiability is close to the derivative there.
* `ConvexOn.continuousAt_fderiv`, `ConvexOn.continuousOn_fderiv`: continuity of the derivative of
  a differentiable convex function.
-/

public section

open Filter Metric Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → ℝ} {L L' : E →L[ℝ] ℝ}
  {x x' : E} {r η : ℝ}

namespace TauCeti

/-- **Subgradients near a point of differentiability.** Suppose `g` is within `η ‖z - x‖` of
`g x + L (z - x)` for every `z` in the ball of radius `r` about `x`, and `L'` is a subgradient of
`g` at a point `x'` within `r / 3` of `x`, on that ball. Then `(L' - L) h ≤ 3 η ‖h‖` for every
`h`. No convexity of `g` is used. -/
theorem apply_sub_apply_le_of_forall_add_le (hr : 0 < r)
    (hexp : ∀ z ∈ ball x r, |g z - g x - L (z - x)| ≤ η * ‖z - x‖)
    (hx' : x' ∈ ball x (r / 3)) (hsub : ∀ z ∈ ball x r, g x' + L' (z - x') ≤ g z) (h : E) :
    L' h - L h ≤ 3 * η * ‖h‖ := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  have hpos : 0 < ‖h‖ := norm_pos_iff.2 hh
  have hη : 0 ≤ η := by
    -- Test the expansion at a point at distance `r / 2` from `x`.
    have hzx : ‖(x + (r / 2 / ‖h‖) • h) - x‖ = r / 2 := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
        div_mul_cancel₀ _ hpos.ne']
    have hz : x + (r / 2 / ‖h‖) • h ∈ ball x r := by
      rw [mem_ball, dist_eq_norm, hzx]
      linarith
    have := (abs_nonneg _).trans (hexp _ hz)
    rw [hzx] at this
    exact (mul_nonneg_iff_of_pos_right (by positivity)).1 this
  set t := r / 3 / ‖h‖
  have ht : 0 < t := by positivity
  have htn : ‖t • h‖ = r / 3 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, div_mul_cancel₀ _ hpos.ne']
  have hx'd : ‖x' - x‖ < r / 3 := by rwa [mem_ball, dist_eq_norm] at hx'
  set z := x' + t • h
  have hzx : z - x = (x' - x) + t • h := by simp only [z]; abel
  have hzn : ‖z - x‖ < 2 * r / 3 := by
    rw [hzx]
    calc ‖x' - x + t • h‖ ≤ ‖x' - x‖ + ‖t • h‖ := norm_add_le _ _
      _ < 2 * r / 3 := by rw [htn]; linarith
  have hz : z ∈ ball x r := by rw [mem_ball, dist_eq_norm]; linarith
  have hx'r : x' ∈ ball x r := by rw [mem_ball, dist_eq_norm]; linarith
  have h₁ := (abs_le.1 (hexp z hz)).2
  have h₂ := (abs_le.1 (hexp x' hx'r)).1
  have hLz : L (z - x) = L (x' - x) + t * L h := by rw [hzx, map_add, map_smul, smul_eq_mul]
  have h₃ : g x' + t * L' h ≤ g z := by
    have h₃ := hsub z hz
    rwa [show z - x' = t • h by simp only [z, add_sub_cancel_left], map_smul,
      smul_eq_mul] at h₃
  rw [hLz] at h₁
  -- Collect: `t (L' h - L h) ≤ η (‖z - x‖ + ‖x' - x‖) ≤ η r`.
  have key : t * (L' h - L h) ≤ η * r := by
    nlinarith [mul_le_mul_of_nonneg_left hzn.le hη, mul_le_mul_of_nonneg_left hx'd.le hη]
  have : L' h - L h ≤ η * r / t := by rw [le_div_iff₀ ht, mul_comm]; exact key
  calc L' h - L h ≤ η * r / t := this
    _ = 3 * η * ‖h‖ := by simp only [t]; field_simp

end TauCeti

/-- **Differentiable convex functions are continuously differentiable at a point.** If `g` is
convex on a neighbourhood `s` of `x` and differentiable at every point near `x`, then its derivative
is continuous at `x`. -/
theorem ConvexOn.continuousAt_fderiv {s : Set E} (hg : ConvexOn ℝ s g) (hs : s ∈ 𝓝 x)
    (hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ g y) : ContinuousAt (fderiv ℝ g) x := by
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  set η := ε / 4
  have hL := (hd.self_of_nhds).hasFDerivAt
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1
    (((show ∀ᶠ y in 𝓝 x, y ∈ s from hs).and hd).and
      (hL.isLittleO.def (show 0 < η by positivity)))
  have hexp : ∀ z ∈ ball x r, |g z - g x - fderiv ℝ g x (z - x)| ≤ η * ‖z - x‖ :=
    fun z hz ↦ by simpa [Real.norm_eq_abs] using (hball z hz).2
  filter_upwards [ball_mem_nhds x (show 0 < r / 3 by positivity)] with x' hx'
  have hx'r : x' ∈ ball x r := ball_subset_ball (by linarith) hx'
  have hsub : ∀ z ∈ ball x r, g x' + fderiv ℝ g x' (z - x') ≤ g z := fun z hz ↦
    hg.add_le_of_hasFDerivWithinAt (hball x' hx'r).1.1 (hball z hz).1.1
      (hball x' hx'r).1.2.hasFDerivAt.hasFDerivWithinAt
  have hbound : ‖fderiv ℝ g x' - fderiv ℝ g x‖ ≤ 3 * η := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h ↦ ?_
    have h₁ := TauCeti.apply_sub_apply_le_of_forall_add_le hr hexp hx' hsub h
    have h₂ := TauCeti.apply_sub_apply_le_of_forall_add_le hr hexp hx' hsub (-h)
    simp only [map_neg, norm_neg] at h₂
    rw [sub_apply, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  rw [dist_eq_norm]
  have hη : η = ε / 4 := rfl
  linarith

/-- **Differentiable convex functions are `C¹`.** A function convex and differentiable on an open
set has a derivative continuous on that set. -/
theorem ConvexOn.continuousOn_fderiv {s : Set E} (hs : IsOpen s) (hg : ConvexOn ℝ s g)
    (hd : DifferentiableOn ℝ g s) : ContinuousOn (fderiv ℝ g) s := fun _ hx ↦
  (hg.continuousAt_fderiv (hs.mem_nhds hx)
    (eventually_of_mem (hs.mem_nhds hx) fun _ hy ↦ hd.differentiableAt (hs.mem_nhds hy)))
    |>.continuousWithinAt
