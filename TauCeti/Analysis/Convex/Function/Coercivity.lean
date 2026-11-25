/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Function.Uniform

import Mathlib.Analysis.Normed.Affine.AddTorsor
import TauCeti.Topology.MetricSpace.LowerBound

/-!
# Lower bounds for strongly convex functions

Positive strong convexity and lower semicontinuity within the domain at a single point
give a global lower bound on the domain.
-/

public section

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s : Set E} {f : E → ℝ} {μ : ℝ} {x : E}

/-- A strongly convex function with positive modulus is bounded below on its domain if it is
lower semicontinuous within the domain at one of its points. -/
theorem StrongConvexOn.bddBelow_image_of_lowerSemicontinuousWithinAt
    (hf : StrongConvexOn s μ f) (hμ : 0 < μ) (hx : x ∈ s)
    (hlsc : LowerSemicontinuousWithinAt f s x) : BddBelow (f '' s) := by
  let g : s → EReal := (fun z : E ↦ (f z : EReal)) ∘ Subtype.val
  let x₀ : s := ⟨x, hx⟩
  have hcoe : LowerSemicontinuousWithinAt (fun z ↦ (f z : EReal)) s x :=
    continuous_coe_real_ereal.continuousAt.comp_lowerSemicontinuousWithinAt hlsc
      EReal.coe_strictMono.monotone
  have hg : LowerSemicontinuousAt g x₀ :=
    lowerSemicontinuousWithinAt_univ_iff.mp
      (LowerSemicontinuousWithinAt.comp (g := ((↑) : s → E))
        (f := fun z : E ↦ (f z : EReal)) (t := Set.univ) (x := x₀) hcoe
        continuous_subtypeVal.continuousWithinAt (fun z _ ↦ z.property))
  have hb := TauCeti.iInf_ne_bot_of_lowerSemicontinuousAt hg (EReal.coe_ne_top _)
    (EReal.coe_ne_bot _) hμ (fun y _ ↦ ?_)
  · obtain ⟨a, _, ha⟩ := EReal.exists_between_coe_real (bot_lt_iff_ne_bot.mpr hb)
    refine ⟨a, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact EReal.coe_le_coe_iff.1 (ha.le.trans (iInf_le g ⟨y, hy⟩))
  · refine ⟨dist x (y : E), fun t ht ↦ ?_⟩
    let z : s := ⟨AffineMap.lineMap x (y : E) t,
      hf.uniformConvexOn.1.lineMap_mem hx y.property ht⟩
    refine ⟨z, ?_, ?_⟩
    · simpa only [x₀, z, Subtype.dist_eq, Real.norm_of_nonneg ht.1] using
        (dist_left_lineMap x (y : E) t).le
    · have hcurve := hf.convexAlong_lineMap hx y.property
      simpa only [g, x₀, z, Function.comp_apply, AffineMap.lineMap_apply_zero,
        AffineMap.lineMap_apply_one] using TauCeti.convexAlong_def.mp hcurve t ht
