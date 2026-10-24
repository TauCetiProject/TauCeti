/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Approach filters in the one-point compactification

The punctured neighbourhoods of a point of the space in its one-point compactification are the
images of its punctured neighbourhoods in the space, so the inclusion preserves them.

Approaching infinity within the image of a set is described by the coclosed-compact filter
restricted to that set. In a pseudometric space, escaping bounded sets gives convergence to
the compactifying point. These facts translate limits in the original space into limits in
its one-point compactification.

The one-point compactification of a proper pseudometric space is first countable: at a point of
the space it inherits the neighbourhood filter of the space, and at infinity the complements of
the closed balls about a fixed point form a countable basis. Being also compact, it is then
sequentially compact, and Fatou-type limit arguments may be run along its neighbourhood filters.
On a proper space the extended distance from a fixed point, with value `⊤` at infinity, is
continuous on the one-point compactification.
-/

public section

open Bornology Filter Set Topology
open scoped OnePoint

namespace TauCeti

namespace OnePoint

/-- The punctured neighbourhoods of a point of `X` in the one-point compactification are the images
of its punctured neighbourhoods in `X`. -/
theorem nhdsNE_coe_eq {X : Type*} [TopologicalSpace X] (x : X) :
    𝓝[≠] (x : OnePoint X) = map (↑) (𝓝[≠] x) := by
  rw [OnePoint.nhdsWithin_coe]
  congr 2
  ext
  simp

/-- The inclusion into the one-point compactification maps punctured neighbourhoods to punctured
neighbourhoods. -/
theorem tendsto_coe_nhdsNE {X : Type*} [TopologicalSpace X] (x : X) :
    Tendsto ((↑) : X → OnePoint X) (𝓝[≠] x) (𝓝[≠] (x : OnePoint X)) :=
  tendsto_map.mono_right (nhdsNE_coe_eq x).ge

end OnePoint

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

/-- The one-point compactification of a proper pseudometric space is first countable. In a proper
space the coclosed-compact filter is the cobounded filter, which is the pullback of `atTop` along
the distance to any fixed point. -/
instance {X : Type*} [PseudoMetricSpace X] [ProperSpace X] :
    FirstCountableTopology (OnePoint X) := by
  refine ⟨fun b ↦ ?_⟩
  induction b using OnePoint.rec with
  | infty =>
    have : (coclosedCompact X).IsCountablyGenerated := by
      cases isEmpty_or_nonempty X with
      | inl _ =>
        rw [Filter.filter_eq_bot_of_isEmpty (coclosedCompact X)]
        infer_instance
      | inr h =>
        rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact,
          ← Metric.comap_dist_right_atTop h.some]
        infer_instance
    rw [OnePoint.nhds_infty_eq]
    infer_instance
  | coe x =>
    rw [OnePoint.nhds_coe_eq]
    infer_instance

/-- On a proper space, the extended distance from a fixed point to a point of the one-point
compactification, with value `⊤` at infinity, is continuous. -/
theorem continuous_elim_edist {X : Type*} [PseudoMetricSpace X] [ProperSpace X] (x : X) :
    Continuous fun b : OnePoint X ↦ b.elim ⊤ (edist x) := by
  refine continuous_iff_continuousAt.2 fun b ↦ ?_
  induction b using OnePoint.rec with
  | infty =>
    refine OnePoint.continuousAt_infty'.2 ?_
    rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    simpa [Function.comp_def, edist_dist] using
      ENNReal.tendsto_ofReal_atTop.comp (Metric.tendsto_dist_left_cobounded_atTop x)
  | coe y =>
    exact OnePoint.continuousAt_coe.2 (continuous_const.edist continuous_id).continuousAt

end TauCeti
