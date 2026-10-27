/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Continuity on a set from a closed graph

A function whose graph over a set `s` is closed and whose values on `s` lie in a compact set is
continuous on `s`. This is the relative form of Mathlib's `continuous_of_isClosed_graph`; it
identifies a bounded single-valued closure of a graph with a continuous function.
-/

public section

open Set

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A function whose graph over `s` is closed and which maps `s` into a compact set is continuous
on `s`. -/
theorem continuousOn_of_isClosed_graphOn {f : X → Y} {s : Set X} {K : Set Y}
    (hf : IsClosed (s.graphOn f)) (hK : IsCompact K) (hfK : MapsTo f s K) :
    ContinuousOn f s := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : s → K := fun x ↦ ⟨f x, hfK x.2⟩
  have hgraph : F.graph = Prod.map Subtype.val Subtype.val ⁻¹' s.graphOn f := by
    ext ⟨x, y⟩
    simp [F, Function.graph, Subtype.ext_iff]
  have hF : Continuous F := continuous_of_isClosed_graph <| by
    rw [hgraph]
    exact hf.preimage (continuous_subtype_val.prodMap continuous_subtype_val)
  exact continuousOn_iff_continuous_domRestrict.mpr (continuous_subtype_val.comp hF)

end TauCeti
