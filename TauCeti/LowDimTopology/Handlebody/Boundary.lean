/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.FrontierProduct
public import TauCeti.LowDimTopology.Handlebody.Basic

/-!
# The boundary surjection for a handlebody

The inclusion of the boundary of the standard genus-`g` handlebody induces a surjection
on fundamental groups at every boundary basepoint. Here the boundary is the frontier of
`handlebody g` in `ℂ × ℝ`, matching the subset formulation of Heegaard splittings.

The product model `planarSurface g × [-1, 1]` makes the geometric argument independent
of a computation of either fundamental group: loops move vertically to an end face, and
points on the side boundary are joined to an end face within the boundary. This is one
of the inputs to the van Kampen proof that a handlebody in a Heegaard splitting generates
the fundamental group of the ambient manifold.

## References

* J. Hempel, *3-Manifolds*, Annals of Mathematics Studies 86, Chapter 2.
* M. Scharlemann, *Heegaard splittings of compact 3-manifolds*, Section 2.
-/

public section

open Set

namespace TauCeti

/-- The boundary inclusion of a standard handlebody is surjective on fundamental groups,
at every boundary basepoint and in every genus, including genus zero. -/
theorem fundamentalGroupMap_frontier_handlebody_surjective (g : ℕ) :
    ∀ z : frontier (handlebody g), Function.Surjective (FundamentalGroup.map
      (ContinuousMap.inclusion (isCompact_handlebody g).isClosed.frontier_subset) z) := by
  -- Transport the subset, its frontier and its inclusion together; the inclusion depends on
  -- the closedness proof, whose type also mentions the subset.
  suffices ∀ (K : Set (ℂ × ℝ)) (hK : IsClosed K),
      K = planarSurface g ×ˢ Icc (-1 : ℝ) 1 →
      ∀ z : frontier K, Function.Surjective (FundamentalGroup.map
        (ContinuousMap.inclusion hK.frontier_subset) z) from
    this _ (isCompact_handlebody g).isClosed (Set.ext fun _ => mem_handlebody)
  rintro K hK rfl
  exact fundamentalGroupMap_frontier_prod_Icc_surjective (isCompact_planarSurface g).isClosed

end TauCeti
