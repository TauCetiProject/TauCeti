/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Topology.MetricSpace.Holder

/-!
# Hölder continuity of a `C¹` function of the point and a Hölder value

A `C¹` function `G` of the point and of the value of a Hölder function `P` is again Hölder on a
small closed ball: the graph map `y ↦ (y, P y)` is Hölder, and `G` is Lipschitz on the compact
convex set where the graph lies. This is the step that makes the right-hand side of a semilinear
elliptic equation Hölder once the solution is.
-/

public section

open Metric Set
open scoped NNReal

namespace TauCeti

/-- A `C¹` function of the point and of the value of a Hölder function `P` is Hölder, with any
exponent `β ≤ 1` smaller than that of `P`, on a closed ball of radius at most `1 / 2`, where all
distances are at most one. -/
theorem exists_holderOnWith_comp_prodMk {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] {G : E × ℝ → ℝ} (hG : ContDiff ℝ 1 G) {P : E → ℝ}
    {C α β : ℝ≥0} {x : E} {r : ℝ} (hr : r ≤ 1 / 2) (hP : HolderOnWith C α P (closedBall x r))
    (hβ : 0 < β) (hβα : β ≤ α) (hβ1 : β ≤ 1) :
    ∃ K, HolderOnWith K β (fun y => G (y, P y)) (closedBall x r) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall x r).exists_bound_of_continuousOn
    (hP.continuousOn (hβ.trans_le hβα))
  obtain ⟨L, hL⟩ := hG.contDiffOn.exists_lipschitzOnWith one_ne_zero
    ((convex_closedBall x r).prod (convex_closedBall (0 : ℝ) M))
    ((isCompact_closedBall x r).prod (isCompact_closedBall (0 : ℝ) M))
  -- The graph map `y ↦ (y, P y)` is `β`-Hölder: distances are at most one on the ball.
  have hgraph : HolderOnWith (max 1 C) β (fun y => (y, P y)) (closedBall x r) := by
    intro y hy y' hy'
    have hd : edist y y' ≤ 1 := by
      rw [edist_dist, ENNReal.ofReal_le_one]
      linarith [dist_triangle_right y y' x, mem_closedBall.1 hy, mem_closedBall.1 hy']
    have h1 : edist y y' ≤ edist y y' ^ (β : ℝ) := by
      simpa using ENNReal.rpow_le_rpow_of_exponent_ge hd (NNReal.coe_le_one.2 hβ1)
    have h2 : edist y y' ^ (α : ℝ) ≤ edist y y' ^ (β : ℝ) :=
      ENNReal.rpow_le_rpow_of_exponent_ge hd (NNReal.coe_le_coe.2 hβα)
    rw [Prod.edist_eq, max_le_iff]
    constructor
    · calc edist y y' ≤ 1 * edist y y' ^ (β : ℝ) := by rwa [one_mul]
        _ ≤ _ := by gcongr; exact_mod_cast le_max_left 1 C
    · calc edist (P y) (P y') ≤ C * edist y y' ^ (α : ℝ) := hP y hy y' hy'
        _ ≤ _ := by gcongr; exact_mod_cast le_max_right 1 C
  refine ⟨L * max 1 C ^ ((1 : ℝ≥0) : ℝ), ?_⟩
  simpa [Function.comp_def] using (holderOnWith_one.2 hL).comp hgraph fun y hy =>
    ⟨hy, mem_closedBall_zero_iff.2 (hM y hy)⟩

end TauCeti
