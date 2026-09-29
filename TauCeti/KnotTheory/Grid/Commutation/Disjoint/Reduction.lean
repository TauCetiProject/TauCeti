/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Disjoint.Sum

/-!
# Reducing the commutation chain-map equation to overlapping domains

The coefficient of a pentagon map composed with a grid differential is a sum over
rectangle--pentagon decompositions. Reversing the order gives a sum over
pentagon--rectangle decompositions. Domains whose vertical side pairs are disjoint
have equal total weights by the commuting bijection. Splitting each finite sum at
`HasDisjointSides` therefore reduces the chain-map equation, coefficient by coefficient,
to domains with a common side.

The reduction is an equivalence: no condition on the overlapping terms is built into
its hypotheses. The remaining geometric argument must pair their weights. The
pentagon--rectangle juxtaposition is described in Ozsváth--Stipsicz--Szabó,
*Grid Homology for Knots and Links*, Section 5.1.
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)
  (R : Type*) [CommRing R]

open Classical in
/-- The rectangle--pentagon and pentagon--rectangle coefficient sums agree exactly when
their overlapping contributions agree. The disjoint contributions cancel by the
commuting-domain pairing. -/
theorem sum_rectanglePentagonWeight_eq_sum_pentagonRectangleWeight_iff_overlap
    (x z : GridState n) :
    (∑ D ∈ G.rectanglePentagonDecompositions C x z,
        G.rectanglePentagonWeight C R D) =
      ∑ D ∈ G.pentagonRectangleDecompositions C x z,
        G.pentagonRectangleWeight C R D ↔
      (∑ D ∈ (G.rectanglePentagonDecompositions C x z).filter
          (fun D => ¬ D.HasDisjointSides), G.rectanglePentagonWeight C R D) =
        ∑ D ∈ (G.pentagonRectangleDecompositions C x z).filter
          (fun D => ¬ D.HasDisjointSides), G.pentagonRectangleWeight C R D := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not
      (G.rectanglePentagonDecompositions C x z) (fun D => D.HasDisjointSides),
    ← Finset.sum_filter_add_sum_filter_not
      (G.pentagonRectangleDecompositions C x z) (fun D => D.HasDisjointSides),
    G.sum_rectanglePentagonWeight_disjoint_eq_sum_pentagonRectangleWeight_disjoint C R x z]
  exact add_left_cancel_iff

open Classical in
/-- On a grid-state generator, the pentagon map commutes with the unblocked
differential exactly when the two sums over common-side domains agree at every
target state. -/
theorem pentagonMap_unblockedDifferential_single_eq_iff_overlap
    (x : GridState n) :
    G.pentagonMap R C (G.unblockedDifferential R (Finsupp.single x 1)) =
        (G.swapColumns C.column (finRotate n C.column)).unblockedDifferential R
          (G.pentagonMap R C (Finsupp.single x 1)) ↔
      ∀ z : GridState n,
        (∑ D ∈ (G.rectanglePentagonDecompositions C x z).filter
            (fun D => ¬ D.HasDisjointSides), G.rectanglePentagonWeight C R D) =
          ∑ D ∈ (G.pentagonRectangleDecompositions C x z).filter
            (fun D => ¬ D.HasDisjointSides), G.pentagonRectangleWeight C R D := by
  rw [G.pentagonMap_unblockedDifferential_single_eq_iff C R x]
  exact forall_congr' fun z =>
    G.sum_rectanglePentagonWeight_eq_sum_pentagonRectangleWeight_iff_overlap C R x z

end TauCeti.GridDiagram
