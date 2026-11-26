/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Liouville

/-!
# Cauchy bounds for Taylor coefficients

On each smaller concentric disc, the coefficients of a holomorphic function satisfy a uniform
geometric upper bound, which can be compared with the contribution of an isolated pole.
-/

public section

open Metric

/-- The norm of the `k`-th Taylor coefficient at the centre of a holomorphic disc is bounded by
`M / r ^ k` at every strictly smaller positive radius `r`, with one `M` for all `k`. -/
theorem DifferentiableOn.exists_norm_iteratedDeriv_div_factorial_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : ℂ → E} {z : ℂ} {r R : ℝ} (hf : DifferentiableOn ℂ f (ball z R))
    (hr : 0 < r) (hrR : r < R) :
    ∃ M : ℝ, ∀ k : ℕ, ‖iteratedDeriv k f z‖ / k.factorial ≤ M / r ^ k := by
  have hsub := closedBall_subset_ball (x := z) hrR
  obtain ⟨M, hM⟩ := (isCompact_sphere z r).exists_bound_of_continuousOn
    (hf.continuousOn.mono (sphere_subset_closedBall.trans hsub))
  refine ⟨M, fun k ↦ (div_le_iff₀ (by positivity)).2 ?_⟩
  calc
    ‖iteratedDeriv k f z‖ ≤ k.factorial * M / r ^ k :=
      Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr (hf.diffContOnCl_ball hsub) hM
    _ = M / r ^ k * k.factorial := by ring
