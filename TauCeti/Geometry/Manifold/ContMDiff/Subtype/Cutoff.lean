/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Normed.Module.Convex
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension

/-!
# Smooth maps into an open set which are the identity near a compact set

For a nonempty convex compact set `K` contained in an open set `U` of a finite-dimensional real
normed space `E`, there is a smooth map `g : E → U` into the open submanifold `U` which agrees with
the identity near every point of `K` (`TopologicalSpace.Opens.exists_contMDiff_eventuallyEq_id`).
It globalizes the inclusion of a convex thickening of `K` inside `U` with
`ContMDiffOn.exists_contMDiff_eventuallyEq_of_starConvex`. Reading a family indexed by `U` through
`g` gives a family indexed by `E` which agrees with it near `K`.
-/

public section

open Filter Set
open scoped ContDiff Manifold Topology

namespace TopologicalSpace.Opens

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **A smooth map `E → U` which is the identity near a convex compact set.** For a nonempty convex
compact set `K` contained in an open set `U` of a finite-dimensional real normed space `E`, there
is a smooth map `g : E → U` which agrees with the identity near every point of `K`. Reading a
family indexed by `U` through `g` gives a family indexed by `E` which agrees with it near `K`. -/
theorem exists_contMDiff_eventuallyEq_id (U : Opens E) {K : Set E} (hKc : Convex ℝ K)
    (hK : IsCompact K) (hKne : K.Nonempty) (hKU : K ⊆ U) :
    ∃ g : E → U, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ g ∧ ∀ x ∈ K, (fun y ↦ (g y : E)) =ᶠ[𝓝 x] id := by
  classical
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_thickening_subset_open U.isOpen hKU
  have hKV : K ⊆ Metric.thickening δ K := Metric.self_subset_thickening hδ K
  obtain ⟨c, hc⟩ := hKne
  -- The inclusion of the thickening into `U`, extended by a constant outside `U`.
  let γ : E → U := fun x ↦ if h : x ∈ U then ⟨x, h⟩ else ⟨c, hKU hc⟩
  have hγ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ γ (Metric.thickening δ K) := by
    rw [← TauCeti.ContMDiffOn.subtypeVal_comp_iff]
    exact contMDiffOn_id.congr fun x hx ↦ by simp [γ, show x ∈ U from hδU hx]
  obtain ⟨g, hg, hgγ⟩ := hγ.exists_contMDiff_eventuallyEq_of_starConvex
    Metric.isOpen_thickening ((hKc.thickening δ).starConvex (hKV hc)) hK.isClosed hKV
  refine ⟨g, hg, fun x hx ↦ ?_⟩
  filter_upwards [hgγ x hx, Metric.isOpen_thickening.mem_nhds (hKV hx)] with y hy hyV
  simp [hy, γ, show y ∈ U from hδU hyV]

end TopologicalSpace.Opens
