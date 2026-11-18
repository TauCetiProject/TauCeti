/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Round balls in a product of normed spaces

The norm of a product `E × F` of seminormed groups is the maximum of the coordinate norms, whose
balls are boxes. Coordinates `z = (q, p)` of `ℂⁿ = ℝⁿ × ℝⁿ`, as in symplectic normal forms, call
instead for the round balls `‖q‖² + ‖p‖² < r²`. This file records that these sets are convex, so
in particular preconnected, and that they form a basis of neighbourhoods of the origin.

## Main results

* `TauCeti.convex_setOf_norm_fst_sq_add_norm_snd_sq_lt`: the set `‖z.1‖² + ‖z.2‖² < c` is
  convex.
* `TauCeti.exists_setOf_norm_fst_sq_add_norm_snd_sq_lt_subset`: every neighbourhood of the
  origin contains a round ball `‖z.1‖² + ‖z.2‖² < r²` with `r > 0`.
-/

public section

namespace TauCeti

open Set Topology

/-- The round ball `‖z.1‖² + ‖z.2‖² < c` of a product of real normed spaces is convex. -/
theorem convex_setOf_norm_fst_sq_add_norm_snd_sq_lt {E F : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] [SeminormedAddCommGroup F] [NormedSpace ℝ F] (c : ℝ) :
    Convex ℝ {z : E × F | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < c} := by
  have hE : ConvexOn ℝ univ fun x : E ↦ ‖x‖ ^ 2 :=
    (convexOn_norm convex_univ).pow (fun _ _ ↦ norm_nonneg _) 2
  have hF : ConvexOn ℝ univ fun x : F ↦ ‖x‖ ^ 2 :=
    (convexOn_norm convex_univ).pow (fun _ _ ↦ norm_nonneg _) 2
  simpa using ((hE.comp_linearMap (LinearMap.fst ℝ E F)).add
    (hF.comp_linearMap (LinearMap.snd ℝ E F))).convex_lt c

/-- Every neighbourhood of the origin of a product of seminormed groups contains a round ball
`‖z.1‖² + ‖z.2‖² < r²` with `r > 0`. -/
theorem exists_setOf_norm_fst_sq_add_norm_snd_sq_lt_subset {E F : Type*} [SeminormedAddGroup E]
    [SeminormedAddGroup F] {U : Set (E × F)} (hU : U ∈ 𝓝 0) :
    ∃ r > 0, {z : E × F | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 < r ^ 2} ⊆ U := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 hU
  refine ⟨r, hr, fun z hz ↦ hball ?_⟩
  have h1 : ‖z.1‖ < r := lt_of_pow_lt_pow_left₀ 2 hr.le (by nlinarith [sq_nonneg ‖z.2‖, hz.out])
  have h2 : ‖z.2‖ < r := lt_of_pow_lt_pow_left₀ 2 hr.le (by nlinarith [sq_nonneg ‖z.1‖, hz.out])
  rw [Metric.mem_ball, dist_zero_right, Prod.norm_def]
  exact max_lt h1 h2

end TauCeti
