/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Approach filters in the one-point compactification

Approaching infinity within the image of a set is described by the coclosed-compact filter
restricted to that set. In a pseudometric space, escaping bounded sets gives convergence to
the compactifying point. These facts translate limits in the original space into limits in
its one-point compactification.
-/

public section

open Bornology Filter Set Topology
open scoped OnePoint

namespace TauCeti

/-- Approaching infinity within the image of a set in the one-point compactification is
equivalent to escaping closed compact sets within the original set. -/
theorem nhdsWithin_infty_coe_image {X : Type*} [TopologicalSpace X] (s : Set X) :
    𝓝[((↑) : X → OnePoint X) '' s] (∞ : OnePoint X) =
      map (↑) (coclosedCompact X ⊓ 𝓟 s) := by
  rw [nhdsWithin, OnePoint.nhds_infty_eq, inf_sup_right]
  have hbot : pure (∞ : OnePoint X) ⊓ 𝓟 (((↑) : X → OnePoint X) '' s) = ⊥ := by
    rw [← principal_singleton, inf_principal]
    simp
  simp only [hbot, sup_bot_eq]
  rw [← map_inf_principal_preimage, preimage_image_eq _ OnePoint.coe_injective]

/-- A map escaping bounded sets in a pseudometric space converges to the compactifying point
after embedding in the one-point compactification. -/
theorem tendsto_coe_infty_of_tendsto_cobounded {α X : Type*} [PseudoMetricSpace X]
    {f : α → X} {l : Filter α} (h : Tendsto f l (cobounded X)) :
    Tendsto (fun x => (f x : OnePoint X)) l (𝓝 ∞) := by
  apply OnePoint.tendsto_coe_infty.comp
  simpa only [coclosedCompact_eq_cocompact] using h.mono_right Metric.cobounded_le_cocompact

end TauCeti
