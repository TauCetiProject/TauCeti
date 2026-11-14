/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic.Module

/-!
# Closures of star-convex sets intersected with closed balls

If a subset `s` of a real seminormed space contains a point `x₀` and is star-convex about `x₀`,
intersecting with any closed ball centred at `x₀` commutes with taking topological closures:
`closure (s ∩ closedBall x₀ r) = closure s ∩ closedBall x₀ r`
(`StarConvex.closure_inter_closedBall`), unconditionally on the radius `r : ℝ`.

Specializing to convex sets and real subspaces gives `Convex.closure_inter_closedBall` and
`Submodule.closure_inter_closedBall_zero`, which pull norm-bounded approximations from the norm
closure of an operator subalgebra back to the subalgebra itself.
-/

public section

open Filter Metric Set
open scoped Topology

section StarConvex

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {x₀ : E}

/-- Intersecting a set containing `x₀` and star-convex about `x₀` with any closed ball centred at
`x₀` commutes with taking closures. -/
theorem StarConvex.closure_inter_closedBall (hs : StarConvex ℝ x₀ s) (hx₀ : x₀ ∈ s) (r : ℝ) :
    closure (s ∩ closedBall x₀ r) = closure s ∩ closedBall x₀ r := by
  refine subset_antisymm
    (closure_inter_subset.trans (inter_subset_inter_right _ isClosed_closedBall.closure_eq.subset))
    fun x ⟨hx, hxr⟩ ↦ ?_
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · exact ((closedBall_eq_empty.2 hr).subset hxr).elim
  · exact mem_closure_iff.2 fun ε hε ↦ ⟨x₀, ⟨hx₀, mem_closedBall_self le_rfl⟩, hxr.trans_lt hε⟩
  · -- Points `(1 - t) • x₀ + t • x` for `t ∈ (0, 1)` lie in `closure s ∩ ball x₀ r` and tend to `x`
    -- as `t → 1`.
    have hne : (𝓝[Ioo (0 : ℝ) 1] 1).NeBot := mem_closure_iff_nhdsWithin_neBot.1 <| by
      rw [closure_Ioo zero_ne_one]
      exact right_mem_Icc.2 zero_le_one
    let g : ℝ → E := fun t ↦ (1 - t) • x₀ + t • x
    have hg1 : g 1 = x := by simp [g]
    have hlim : Tendsto g (𝓝[Ioo (0 : ℝ) 1] 1) (𝓝 x) :=
      hg1 ▸ ((Continuous.tendsto (by fun_prop) 1).mono_left nhdsWithin_le_nhds)
    refine isClosed_closure.mem_of_tendsto hlim (eventually_nhdsWithin_of_forall fun t ht ↦ ?_)
    have hmem_cl : g t ∈ closure s :=
      map_mem_closure (f := fun y ↦ (1 - t) • x₀ + t • y) (by fun_prop) hx
        fun y hy ↦ hs hy (sub_nonneg.2 ht.2.le) ht.1.le (sub_add_cancel 1 t)
    have hmem_ball : g t ∈ ball x₀ r := by
      have hsub : g t - x₀ = t • (x - x₀) := by simp only [g]; module
      rw [mem_ball, dist_eq_norm, hsub, norm_smul, Real.norm_of_nonneg ht.1.le, ← dist_eq_norm]
      calc t * dist x x₀ ≤ t * r := mul_le_mul_of_nonneg_left hxr ht.1.le
        _ < 1 * r := mul_lt_mul_of_pos_right ht.2 hr
        _ = r := one_mul r
    exact closure_mono (inter_subset_inter_right _ ball_subset_closedBall)
      (isOpen_ball.closure_inter ⟨hmem_cl, hmem_ball⟩)

/-- Intersecting a convex set containing `x₀` with any closed ball centred at `x₀` commutes with
taking closures. -/
theorem Convex.closure_inter_closedBall (hs : Convex ℝ s) (hx₀ : x₀ ∈ s) (r : ℝ) :
    closure (s ∩ closedBall x₀ r) = closure s ∩ closedBall x₀ r :=
  (hs.starConvex hx₀).closure_inter_closedBall hx₀ r

/-- Intersecting a real subspace with any closed ball centred at `0` commutes with taking
closures. -/
theorem Submodule.closure_inter_closedBall_zero (p : Submodule ℝ E) (r : ℝ) :
    closure ((p : Set E) ∩ closedBall 0 r) = closure (p : Set E) ∩ closedBall 0 r :=
  p.convex.closure_inter_closedBall p.zero_mem r

end StarConvex
