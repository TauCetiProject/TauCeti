/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.ODE.ExistUnique

/-!
# A uniform time of existence for autonomous ODEs

Picard–Lindelöf produces a solution of `x' = g x` through a single initial point. Extending an
integral curve past a finite endpoint of its interval of definition needs more: a *single* time
`ε > 0` that works for **every** initial point near a given one and every initial time, together
with control on where the resulting solutions go. This file supplies both by shrinking Mathlib's
Picard–Lindelöf solution space until all of its curves lie in a prescribed neighbourhood.

## Main results

* `ContDiffAt.exists_forall_mem_ball_exists_eq_forall_mem_Ioo_hasDerivAt_and_mem`: for a `C^1`
  autonomous vector field and a neighbourhood `u` of `c`, there are a radius `r > 0` and a time
  `ε > 0` such that, for every initial time `t₀`, every initial point of `ball c r` carries a
  solution on `Ioo (t₀ - ε) (t₀ + ε)` staying in `u`.
-/

public section

open Filter Metric ODE Set
open scoped NNReal Topology

namespace ContDiffAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {g : E → E} {c : E} {u : Set E}

/-- **Uniform time of existence.** For an autonomous vector field `g` that is `C^1` at `c` and a
neighbourhood `u` of `c`, there are a radius `r > 0` and a time `ε > 0` such that, for every
initial time `t₀`, every initial point in `ball c r` carries a solution of `f' t = g (f t)` on all
of `Ioo (t₀ - ε) (t₀ + ε)`, which moreover stays inside `u`.

Picard–Lindelöf alone gives a time of existence depending on the initial point; the content here
is that it can be chosen uniformly, and that the solutions do not escape a prescribed
neighbourhood. -/
theorem exists_forall_mem_ball_exists_eq_forall_mem_Ioo_hasDerivAt_and_mem
    (hg : ContDiffAt ℝ 1 g c) (hu : u ∈ 𝓝 c) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ t₀ : ℝ, ∀ x ∈ ball c r, ∃ f : ℝ → E, f t₀ = x ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt f (g (f t)) t ∧ f t ∈ u := by
  obtain ⟨ε₀, hε₀, a, r₀, L, K, hr₀, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hg
  obtain ⟨ρ, hρ, hρu⟩ := nhds_basis_closedBall.mem_iff.mp hu
  -- the ball of radius `a` on which the Picard–Lindelöf data lives is nondegenerate
  have ha : 0 < a := by
    have h := (hpl 0).mul_max_le
    simp only [zero_add, zero_sub, sub_zero, neg_neg, max_self] at h
    have : (0 : ℝ) < r₀ := hr₀
    have : (0 : ℝ) ≤ L * ε₀ := by positivity
    exact_mod_cast (by linarith : (0 : ℝ) < a)
  -- shrink the ball so that it sits inside `u`, and shrink the time accordingly
  set a' : ℝ≥0 := min a ρ.toNNReal
  have ha' : 0 < a' := lt_min ha (Real.toNNReal_pos.mpr hρ)
  have ha'u : closedBall c a' ⊆ u :=
    (closedBall_subset_closedBall (by simp [a', hρ.le])).trans hρu
  obtain ⟨ε, hε, hpl'⟩ :=
    (hpl 0).exists_shrink_radius hε₀ (min_le_left a _) (half_lt_self ha')
  refine ⟨a' / 2, by positivity, ε, hε, fun t₀ x hx ↦ ?_⟩
  obtain ⟨α, hα⟩ := FunSpace.exists_isFixedPt_next hpl' (ball_subset_closedBall hx)
  have h0 : (0 : ℝ) ∈ Icc (0 - ε) (0 + ε) := by simp [hε.le]
  -- solve with initial time `0`, then translate to initial time `t₀`: the field is autonomous
  refine ⟨fun t ↦ α.compProj (t - t₀), ?_, fun t ht ↦
    ⟨?_, ha'u (α.compProj_mem_closedBall hpl'.mul_max_le)⟩⟩
  · beta_reduce
    rw [sub_self, FunSpace.compProj_of_mem h0, ← hα, FunSpace.next_apply₀]
  have hs : t - t₀ ∈ Ioo (0 - ε) (0 + ε) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine HasDerivAt.comp_sub_const t t₀ <| (hasDerivWithinAt_picard_Icc h0
    hpl'.continuousOn_uncurry α.continuous_compProj.continuousOn
    (fun _ _ ↦ α.compProj_mem_closedBall hpl'.mul_max_le) x (Ioo_subset_Icc_self hs)
    |>.congr_of_mem (fun t' ht' ↦ ?_) (Ioo_subset_Icc_self hs)).hasDerivAt
      (Icc_mem_nhds hs.1 hs.2)
  nth_rw 1 [← hα]
  rw [FunSpace.compProj_of_mem ht', FunSpace.next_apply]

end ContDiffAt
