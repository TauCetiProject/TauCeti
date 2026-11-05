/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Order.OrderClosed

/-!
# Continuous extension of convexity to the closure

The convexity inequality passes to the closure when the function is continuous there.
This removes a separate closure-convexity hypothesis from supporting-contact estimates.
-/

public section

open Set

/-- A convex function that is continuous on the closure remains convex on that closure. -/
theorem ConvexOn.closure_of_continuousOn {𝕜 E F : Type*} [Field 𝕜] [PartialOrder 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousConstSMul 𝕜 E] [AddCommMonoid F] [PartialOrder F] [SMul 𝕜 F]
    [TopologicalSpace F] [ContinuousAdd F] [ContinuousConstSMul 𝕜 F] [OrderClosedTopology F]
    {s : Set E} {f : E → F} (hf : ConvexOn 𝕜 s f) (hc : ContinuousOn f (closure s)) :
    ConvexOn 𝕜 (closure s) f := by
  refine ⟨hf.1.closure, ?_⟩
  intro x hx y hy a b ha hb hab
  have hl : ContinuousOn (fun p : E × E => f (a • p.1 + b • p.2)) (closure (s ×ˢ s)) := by
    rw [closure_prod_eq]
    exact hc.comp ((continuous_fst.const_smul a).add
      (continuous_snd.const_smul b)).continuousOn
      (fun _ hp => hf.1.closure hp.1 hp.2 ha hb hab)
  have hr : ContinuousOn (fun p : E × E => a • f p.1 + b • f p.2) (closure (s ×ˢ s)) := by
    rw [closure_prod_eq]
    exact ((hc.comp continuousOn_fst
      fun _ (hp : _ ∈ closure s ×ˢ closure s) => hp.1).const_smul a).add
      ((hc.comp continuousOn_snd
        fun _ (hp : _ ∈ closure s ×ˢ closure s) => hp.2).const_smul b)
  exact le_on_closure (s := s ×ˢ s) (x := (x, y))
    (fun _ (hp : _ ∈ s ×ˢ s) => hf.2 hp.1 hp.2 ha hb hab) hl hr
    (by rw [closure_prod_eq]; exact ⟨hx, hy⟩)
