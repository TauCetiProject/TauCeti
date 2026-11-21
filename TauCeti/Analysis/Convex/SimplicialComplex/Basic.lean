/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.SimplicialComplex.Basic

/-!
# Vertices of geometric simplicial complexes

Points of faces are vertices, and the vertex set is monotone under inclusion of complexes.
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

end Geometry.SimplicialComplex
