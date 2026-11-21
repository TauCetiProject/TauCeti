/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import Mathlib.Analysis.Convex.Topology

/-!
# Vertices and underlying spaces of geometric simplicial complexes

Points of faces are vertices, and the vertex set is monotone under inclusion of complexes. The
underlying space of a complex whose closed simplices form a locally finite family is closed.
-/

public section

namespace Geometry.SimplicialComplex

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  {K : SimplicialComplex 𝕜 E}

/-- Every point of a face of a geometric complex is a vertex. -/
theorem mem_vertices_of_mem_faces {s : Finset E} (hs : s ∈ K.faces) {x : E} (hx : x ∈ s) :
    x ∈ K.vertices :=
  K.down_closed hs (Finset.singleton_subset_iff.mpr hx) (Finset.singleton_nonempty x)

/-- The vertices of a subcomplex are vertices of the larger complex. -/
theorem vertices_mono {L : SimplicialComplex 𝕜 E} (h : K ≤ L) : K.vertices ⊆ L.vertices :=
  fun _ hx => h hx

/-- The underlying space of a geometric complex in a Hausdorff space is closed when its closed
simplices form a locally finite family: it is a locally finite union of compact convex hulls. -/
theorem isClosed_space_of_locallyFinite {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderClosedTopology 𝕜] [CompactIccSpace 𝕜]
    [IsTopologicalRing 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] {K : SimplicialComplex 𝕜 E}
    (hK : LocallyFinite fun s : K.faces => convexHull 𝕜 (s : Set E)) : IsClosed K.space := by
  rw [space, Set.biUnion_eq_iUnion]
  exact hK.isClosed_iUnion fun s => s.val.finite_toSet.isClosed_convexHull 𝕜

end Geometry.SimplicialComplex
