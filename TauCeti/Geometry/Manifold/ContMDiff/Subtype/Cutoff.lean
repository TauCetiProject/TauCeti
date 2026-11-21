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
# Smooth maps into an open set which are the identity near a compact set

For a nonempty convex compact set `K` contained in an open set `U` of a finite-dimensional real
normed space `E`, there is a smooth map `g : E → U` into the open submanifold `U` which agrees with
the identity near every point of `K` (`TopologicalSpace.Opens.exists_contMDiff_eventuallyEq_id`).
It is the map `Convex.exists_contDiff_mem_eventuallyEq_id` built from a smooth cutoff, read as a
map into `U`. Reading a family indexed by `U` through `g` gives a family indexed by `E` which agrees
with it near `K`.
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
  obtain ⟨κ, hκ, hκU, hκid⟩ := hKc.exists_contDiff_mem_eventuallyEq_id hK hKne U.isOpen hKU
  refine ⟨fun y ↦ ⟨κ y, hκU y⟩, ?_, hκid⟩
  rw [← TauCeti.ContMDiff.subtypeVal_comp_iff]
  exact hκ.contMDiff

end TopologicalSpace.Opens
