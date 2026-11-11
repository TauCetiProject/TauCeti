/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Continuous
import Mathlib.Tactic.Linarith

/-!
# Continuity of monotone convex functions on a half-line

A function `Φ : ℝ → ℝ` that is convex and monotone on `[a, ∞)` is continuous there, including at
the endpoint `a` (`ConvexOn.continuousOn_Ici_of_monotoneOn`). Convexity alone gives continuity on
`(a, ∞)`; monotonicity squeezes `Φ` at `a` between `Φ a` and the chord from `a` to `a + 1`.
-/

public section

open Set Filter

open scoped Topology

namespace ConvexOn

/-- A monotone function that is convex on `[a, ∞)` is continuous there, including at `a`. -/
theorem continuousOn_Ici_of_monotoneOn {a : ℝ} {Φ : ℝ → ℝ} (hΦ : ConvexOn ℝ (Ici a) Φ)
    (hΦm : MonotoneOn Φ (Ici a)) : ContinuousOn Φ (Ici a) := by
  refine hΦ.continuousOn_Ici ?_
  have hub : Tendsto (fun t : ℝ ↦ Φ a + (t - a) * (Φ (a + 1) - Φ a)) (𝓝[Ici a] a)
      (𝓝 (Φ a)) := by
    have hc : Continuous fun t : ℝ ↦ Φ a + (t - a) * (Φ (a + 1) - Φ a) := by fun_prop
    simpa using (hc.tendsto a).mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact hΦm (mem_Ici.2 le_rfl) ht ht
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iic_mem_nhds (lt_add_one a))] with t ht ht1
    have h := hΦ.2 (mem_Ici.2 le_rfl) (mem_Ici.2 (lt_add_one a).le)
      (sub_nonneg.2 (sub_le_iff_le_add'.2 (mem_Iic.1 ht1))) (sub_nonneg.2 (mem_Ici.1 ht))
      (by ring)
    have hpt : (1 - (t - a)) • a + (t - a) • (a + 1) = t := by
      simp only [smul_eq_mul]
      ring
    rw [hpt] at h
    simp only [smul_eq_mul] at h
    linarith

end ConvexOn
