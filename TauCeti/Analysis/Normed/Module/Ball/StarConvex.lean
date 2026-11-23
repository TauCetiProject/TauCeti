/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.Basic
import TauCeti.Analysis.Normed.Module.Ball.Retraction

/-!
# Closures of star-convex sets intersected with closed balls

If a subset `s` of a real seminormed space is star-convex about `x₀`, intersecting with any closed
ball centred at `x₀` commutes with taking topological closures:
`closure (s ∩ closedBall x₀ r) = closure s ∩ closedBall x₀ r`
(`StarConvex.closure_inter_closedBall`), unconditionally on the radius `r : ℝ` (including when
`s = ∅`).

Specializing to convex sets and real subspaces gives `Convex.closure_inter_closedBall` and
`Submodule.closure_inter_closedBall_zero`, which pull norm-bounded approximations from the norm
closure of an operator subalgebra back to the subalgebra itself.
-/

public section

open Filter Metric Set
open scoped Topology

section StarConvex

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {x₀ : E}

/-- Intersecting a set star-convex about `x₀` with any closed ball centred at `x₀` commutes with
taking closures. -/
theorem StarConvex.closure_inter_closedBall (hs : StarConvex ℝ x₀ s) (r : ℝ) :
    closure (s ∩ closedBall x₀ r) = closure s ∩ closedBall x₀ r := by
  refine subset_antisymm
    (closure_inter_subset.trans (inter_subset_inter_right _ isClosed_closedBall.closure_eq.subset))
    fun x ⟨hx, hxr⟩ ↦ ?_
  rcases lt_or_ge r 0 with hr | hr
  · exact ((closedBall_eq_empty.2 hr).subset hxr).elim
  · by_cases hx0 : dist x x₀ = 0
    · exact mem_closure_iff.2 fun ε hε ↦
        ⟨x₀, ⟨hs.mem (closure_nonempty_iff.1 ⟨x, hx⟩), mem_closedBall_self hr⟩,
          hx0.trans_lt hε⟩
    · have hmem := map_mem_closure (f := TauCeti.centeredRadialRetraction x₀ r)
        (TauCeti.lipschitzWith_centeredRadialRetraction hr).continuous hx
        (t := s ∩ closedBall x₀ r) fun y hy ↦
          ⟨?_, TauCeti.centeredRadialRetraction_mem_closedBall hr y⟩
      · rwa [TauCeti.centeredRadialRetraction_of_dist_pos_of_dist_le
          (lt_of_le_of_ne dist_nonneg (Ne.symm hx0)) hxr] at hmem
      · by_cases hy0 : dist y x₀ = 0
        · rw [TauCeti.centeredRadialRetraction_of_dist_eq_zero hy0]
          exact hs.mem ⟨y, hy⟩
        · rcases le_or_gt (dist y x₀) r with hyr | hyr
          · rwa [TauCeti.centeredRadialRetraction_of_dist_pos_of_dist_le
              (lt_of_le_of_ne dist_nonneg (Ne.symm hy0)) hyr]
          · rw [TauCeti.centeredRadialRetraction_of_le_dist hyr.le]
            exact hs.add_smul_sub_mem hy (div_nonneg hr dist_nonneg)
              ((div_le_one (lt_of_le_of_ne dist_nonneg (Ne.symm hy0))).2 hyr.le)

/-- Intersecting a convex set containing `x₀` with any closed ball centred at `x₀` commutes with
taking closures. -/
theorem Convex.closure_inter_closedBall (hs : Convex ℝ s) (hx₀ : x₀ ∈ s) (r : ℝ) :
    closure (s ∩ closedBall x₀ r) = closure s ∩ closedBall x₀ r :=
  (hs.starConvex hx₀).closure_inter_closedBall r

/-- Intersecting a real subspace with any closed ball centred at `0` commutes with taking
closures. -/
theorem Submodule.closure_inter_closedBall_zero (p : Submodule ℝ E) (r : ℝ) :
    closure ((p : Set E) ∩ closedBall 0 r) = closure (p : Set E) ∩ closedBall 0 r :=
  p.convex.closure_inter_closedBall p.zero_mem r

end StarConvex
