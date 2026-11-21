/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Smooth maps into an open set of times which are the identity near a compact set

For a nonempty convex compact set `K` of times contained in an open set `J ⊆ ℝ`, there is a smooth
map `g : ℝ → J` into the open submanifold `J` which agrees with the identity near every time of `K`
(`TopologicalSpace.Opens.exists_contMDiff_eventuallyEq_id`). It is the map
`Convex.exists_contDiff_mem_eventuallyEq_id` built from a smooth cutoff, read as a map into `J`.
Reading a family indexed by `J` through `g` gives a family indexed by `ℝ` which agrees with it near
`K`.
-/

public section

open Filter Set
open scoped ContDiff Manifold Topology

namespace TopologicalSpace.Opens

/-- **A smooth map `ℝ → J` which is the identity near a convex compact set of times.** For a
nonempty convex compact set `K` of times contained in an open set `J` of times, there is a smooth
map `g : ℝ → J` which agrees with the identity near every time of `K`. Reading a family indexed by
`J` through `g` gives a family indexed by `ℝ` which agrees with it near `K`. -/
theorem exists_contMDiff_eventuallyEq_id (J : Opens ℝ) {K : Set ℝ} (hKc : Convex ℝ K)
    (hK : IsCompact K) (hKne : K.Nonempty) (hKJ : K ⊆ J) :
    ∃ g : ℝ → J, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ g ∧ ∀ u ∈ K, (fun v ↦ (g v : ℝ)) =ᶠ[𝓝 u] id := by
  obtain ⟨κ, hκ, hκJ, hκid⟩ := hKc.exists_contDiff_mem_eventuallyEq_id hK hKne J.isOpen hKJ
  refine ⟨fun v ↦ ⟨κ v, hκJ v⟩, ?_, hκid⟩
  rw [← TauCeti.ContMDiff.subtypeVal_comp_iff]
  exact hκ.contMDiff

end TopologicalSpace.Opens
