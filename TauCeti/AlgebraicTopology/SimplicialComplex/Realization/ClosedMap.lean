/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Basic

/-!
# Closed maps into weak polyhedra

A continuous map into a weak simplicial realization is closed if the inverse image of each
closed simplex is compact. This criterion proves continuity of inverse subdivision maps without
requiring the whole polyhedron to be finite or locally finite.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2
  (the weak topology on polyhedra).
-/

public section

open Set TauCeti.SetLike

namespace AbstractSimplicialComplex

variable {ι X : Type*} [TopologicalSpace X] {K : AbstractSimplicialComplex ι}

/-- A continuous map into a weak realization is closed if the inverse image of every closed
simplex is compact. No local finiteness assumption on the target complex is needed. -/
theorem isClosedMap_of_isCompact_preimage_faceInclusion {f : X → Realization K}
    (hf : Continuous f)
    (hcompact : ∀ σ : Face K, IsCompact (f ⁻¹' range (faceInclusion K σ))) :
    IsClosedMap f := by
  intro C hC
  apply isClosed_iff_faceInclusion.mpr
  intro σ
  simpa only [Set.image_preimage_inter, Set.preimage_range_inter] using
    (((hcompact σ).inter_right hC).image hf).isClosed.preimage (continuous_faceInclusion K σ)

end AbstractSimplicialComplex
