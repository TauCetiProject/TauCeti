/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import TauCeti.Analysis.Calculus.FDeriv.Remainder

/-!
# Interior tangent balls at a regular level

At a regular point of a twice continuously differentiable real function, the strict sublevel
contains an open ball tangent to the level set, inside any prescribed neighborhood of the point.
This gives the interior sphere condition at a regular level set used by the Hopf boundary lemma.
-/

public section

open Filter InnerProductSpace Metric Set
open scoped Gradient NNReal RealInnerProductSpace Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {f : E → ℝ} {x : E}

/-- An arbitrarily small interior tangent ball for the strict sublevel at a regular point. -/
theorem ContDiffAt.exists_ball_subset_lt_of_fderiv_ne_zero (hf : ContDiffAt ℝ 2 f x)
    (hreg : fderiv ℝ f x ≠ 0) {U : Set E} (hU : U ∈ 𝓝 x) :
    ∃ y : E, ∃ r > 0, x ∈ sphere y r ∧ ball y r ⊆ {z | f z < f x} ∩ U := by
  have hg : 0 < ‖∇ f x‖ := norm_pos_iff.mpr fun h ↦ hreg (by rw [← toDual_gradient, h, map_zero])
  obtain ⟨δ, hδ, K, hTaylor⟩ := isCompact_singleton.exists_pos_forall_norm_sub_sub_fderiv_sub_le_mul
    (F := fun (_ : ℝ) ↦ f) (x := fun _ ↦ x) (K := {0})
    (fun _ _ ↦ hf.comp _ contDiffAt_snd) continuousOn_const
  obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff_ball.mp
    ((Filter.eventually_mem_set.mpr (ball_mem_nhds x hδ)).and
      (Filter.eventually_mem_set.mpr hU))
  let t := min (ε / 2 / ‖∇ f x‖) (1 / (2 * (|K| + 1)))
  have ht : 0 < t := lt_min (by positivity) (by positivity)
  have htε : t * ‖∇ f x‖ ≤ ε / 2 := (le_div_iff₀ hg).mp (min_le_left _ _)
  have htK : t * (2 * (|K| + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  set y := x - t • ∇ f x with hy
  set r := t * ‖∇ f x‖ with hrdef
  have hr : 0 < r := mul_pos ht hg
  have hxy : dist x y = r := by simp [hy, hrdef, norm_smul, abs_of_pos ht]
  refine ⟨y, r, hr, mem_sphere.mpr hxy, ?_⟩
  intro z hz
  have hzx : dist z x < ε := by
    have h := dist_triangle z y x
    rw [dist_comm y x, hxy] at h
    linarith [mem_ball.mp hz]
  refine ⟨?_, (hnear z hzx).2⟩
  set d := z - x with hd
  have hlin : f z - f x - ⟪d, ∇ f x⟫_ℝ ≤ K * ‖d‖ ^ 2 := by
    have h := hTaylor 0 (mem_singleton 0) d 0
      (by rw [hd, ← dist_eq_norm]; exact (mem_ball.mp (hnear z hzx).1).le)
      (by simpa using hδ.le)
    rw [real_inner_comm, inner_gradient_left]
    exact (le_abs_self _).trans (by simpa [hd, sq, mul_assoc] using h)
  have hnorm : ‖d + t • ∇ f x‖ < r := by
    simpa only [hd, hy, mem_ball, dist_eq_norm, sub_sub_eq_add_sub, sub_add_eq_add_sub] using hz
  have hsq := sq_lt_sq' (by linarith [norm_nonneg (d + t • ∇ f x)]) hnorm
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_of_nonneg ht.le, hrdef] at hsq
  have hcoef : (2 * t) * K ≤ 1 := by
    nlinarith [mul_le_mul_of_nonneg_left (le_abs_self K) ht.le]
  have hbound := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖d‖)
  -- The sphere inequality gives ⟪d, ∇ f x⟫ < -‖d‖² / (2t) ≤ -K‖d‖².
  have hdecrease : ⟪d, ∇ f x⟫_ℝ < -K * ‖d‖ ^ 2 := by
    have ht2 : 0 < 2 * t := by positivity
    apply (mul_lt_mul_iff_right₀ ht2).mp
    nlinarith
  rw [mem_ofPred_eq]
  linarith
