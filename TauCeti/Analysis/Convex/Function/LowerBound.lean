/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Strong

import Mathlib.Analysis.Normed.Affine.AddTorsor
import TauCeti.Analysis.Convex.Function.Along
import TauCeti.Topology.MetricSpace.Pseudo.LowerBound

/-!
# Lower bounds for strongly convex functions

Positive strong convexity and a local lower bound within the domain at a single
point give a global lower bound on the domain.
-/

public section

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s : Set E} {f : E → ℝ} {μ : ℝ} {x : E}

/-- A strongly convex function with positive modulus is bounded below on its domain if it
has a local lower bound within the domain at one of its points. -/
theorem StrongConvexOn.bddBelow_image_of_eventually_le
    (hf : StrongConvexOn s μ f) (hμ : 0 < μ) (hx : x ∈ s) {L : ℝ}
    (hlow : ∀ᶠ y in 𝓝[s] x, L ≤ f y) : BddBelow (f '' s) := by
  let g : s → EReal := fun y ↦ f y
  let x₀ : s := ⟨x, hx⟩
  have hg : ∀ᶠ y in 𝓝 x₀, (L : EReal) ≤ g y := by
    rw [nhdsWithin_eq_map_subtypeVal hx, eventually_map] at hlow
    exact hlow.mono fun _ hy ↦ EReal.coe_le_coe_iff.2 hy
  have hb := TauCeti.iInf_ne_bot_of_eventually_le hg (EReal.coe_ne_top _) hμ (fun y _ ↦ ?_)
  · obtain ⟨a, _, ha⟩ := EReal.exists_between_coe_real (bot_lt_iff_ne_bot.mpr hb)
    refine ⟨a, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact EReal.coe_le_coe_iff.1 (ha.le.trans (iInf_le g ⟨y, hy⟩))
  · refine ⟨dist x (y : E), fun t ht ↦ ?_⟩
    let z : s := ⟨AffineMap.lineMap x (y : E) t,
      hf.1.lineMap_mem hx y.property ht⟩
    refine ⟨z, ?_, ?_⟩
    · simpa only [x₀, z, Subtype.dist_eq, Real.norm_of_nonneg ht.1] using
        (dist_left_lineMap x (y : E) t).le
    · have hcurve := hf.convexAlong_lineMap hx y.property
      simpa only [g, x₀, z, AffineMap.lineMap_apply_zero,
        AffineMap.lineMap_apply_one] using TauCeti.convexAlong_def.mp hcurve t ht
