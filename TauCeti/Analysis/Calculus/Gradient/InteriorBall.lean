/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Interior tangent balls at a regular level

At a regular point of a twice continuously differentiable real function, the strict sublevel
contains an open ball tangent to the level set. The center lies in the direction opposite the
gradient. The ball can be taken inside any prescribed neighborhood of the point.
-/

public section

open Filter InnerProductSpace Metric Set
open scoped Gradient NNReal RealInnerProductSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {x : E}

private theorem eventually_taylor_bound (hf : ContDiffAt ℝ 2 f x) :
    ∃ K : ℝ≥0, ∀ᶠ z in 𝓝 x,
      f z - f x - ⟪z - x, ∇ f x⟫_ℝ ≤ K * ‖z - x‖ ^ 2 := by
  obtain ⟨K, V, hV, hLip⟩ := (hf.fderiv_right (m := 1) (by norm_num)).exists_lipschitzOnWith
  have hd : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ f z :=
    (hf.eventually (by norm_num)).mono fun _ h ↦ h.differentiableAt (by norm_num)
  obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff_ball.mp ((show ∀ᶠ z in 𝓝 x, z ∈ V from hV).and hd)
  refine ⟨K, Metric.eventually_nhds_iff_ball.mpr ⟨ε, hε, fun z hzx ↦ ?_⟩⟩
  let d := z - x
  have hsub : closedBall x ‖d‖ ⊆ ball x ε := by
    intro p hp
    exact (mem_closedBall.mp hp).trans_lt (by simpa [d, dist_eq_norm] using hzx)
  have hTaylor := (convex_closedBall x ‖d‖).norm_image_sub_le_of_norm_fderiv_le'
    (𝕜 := ℝ) (f := f) (φ := fderiv ℝ f x) (C := (K : ℝ) * ‖d‖)
    (fun p hp ↦ (hnear p (hsub hp)).2) (fun p hp ↦ by
      calc
        ‖fderiv ℝ f p - fderiv ℝ f x‖ ≤ K * dist p x := by
          simpa only [dist_eq_norm] using
            hLip.dist_le_mul p (hnear p (hsub hp)).1 x (mem_of_mem_nhds hV)
        _ ≤ K * ‖d‖ := by gcongr; exact mem_closedBall.mp hp)
    (mem_closedBall_self (norm_nonneg _))
    (show z ∈ closedBall x ‖d‖ by simp [d, mem_closedBall, dist_eq_norm])
  rw [real_inner_comm, inner_gradient_left]
  simpa only [d, sq, mul_assoc] using (le_abs_self _).trans hTaylor

/-- An arbitrarily small interior tangent ball for the strict sublevel at a regular point. -/
theorem ContDiffAt.exists_ball_subset_lt_of_fderiv_ne_zero (hf : ContDiffAt ℝ 2 f x)
    (hreg : fderiv ℝ f x ≠ 0) {U : Set E} (hU : U ∈ 𝓝 x) :
    ∃ y : E, ∃ r > 0, x ∈ sphere y r ∧ ball y r ⊆ {z | f z < f x} ∩ U := by
  have hg : 0 < ‖∇ f x‖ := norm_pos_iff.mpr fun h ↦ hreg (by rw [← toDual_gradient, h, map_zero])
  obtain ⟨K, hTaylor⟩ := eventually_taylor_bound hf
  obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff_ball.mp (hTaylor.and hU)
  let t := min (ε / 2 / ‖∇ f x‖) (1 / (2 * ((K : ℝ) + 1)))
  have ht : 0 < t := lt_min (by positivity) (by positivity)
  have htε : t * ‖∇ f x‖ ≤ ε / 2 := (le_div_iff₀ hg).mp (min_le_left _ _)
  have htK : t * (2 * ((K : ℝ) + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  let y := x - t • ∇ f x
  let r := t * ‖∇ f x‖
  have hr : 0 < r := mul_pos ht hg
  have hxy : dist x y = r := by simp [y, r, norm_smul, abs_of_pos ht]
  refine ⟨y, r, hr, mem_sphere.mpr hxy, ?_⟩
  intro z hz
  have hzx : dist z x < ε := by
    have h := dist_triangle z y x
    rw [dist_comm y x, hxy] at h
    linarith [mem_ball.mp hz, show r ≤ ε / 2 from htε]
  refine ⟨?_, (hnear z hzx).2⟩
  let d := z - x
  have hlin := (hnear z hzx).1
  change f z - f x - ⟪d, ∇ f x⟫_ℝ ≤ (K : ℝ) * ‖d‖ ^ 2 at hlin
  have hnorm : ‖d + t • ∇ f x‖ < r := by
    simpa only [d, y, mem_ball, dist_eq_norm, sub_sub_eq_add_sub, sub_add_eq_add_sub] using hz
  have hsq := sq_lt_sq' (by linarith [norm_nonneg (d + t • ∇ f x)]) hnorm
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_of_nonneg ht.le] at hsq
  have hcoef : (2 * t) * (K : ℝ) ≤ 1 := by linarith
  have hbound := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖d‖)
  change f z < f x
  by_contra! h
  have h' := mul_le_mul_of_nonneg_left (show -⟪d, ∇ f x⟫_ℝ ≤ (K : ℝ) * ‖d‖ ^ 2 by linarith)
    (show 0 ≤ 2 * t by positivity)
  dsimp only [r] at hsq
  nlinarith
