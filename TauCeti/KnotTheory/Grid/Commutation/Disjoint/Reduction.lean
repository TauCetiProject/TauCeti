/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.ChainMap
public import TauCeti.KnotTheory.Grid.Commutation.Disjoint.Sum
public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Disjoint

/-!
# Reducing the commutation chain-map equation to overlapping domains

The coefficient of a pentagon map composed with a grid differential is a sum over
rectangle--pentagon decompositions. Reversing the order gives a sum over
pentagon--rectangle decompositions. Domains whose vertical side pairs are disjoint
have equal total weights by the commuting bijection. Splitting each finite sum at
`HasDisjointSides` therefore reduces the chain-map equation, coefficient by coefficient,
to domains with a common side.

The reduction is an equivalence: no condition on the overlapping terms is built into
its hypotheses. It is first stated for `GridDiagram.pentagonMap` alone, which counts only the
pentagons turning on their terminal side and is not a chain map by itself. The same splitting,
together with the disjoint-side pairing for pentagons turning on their initial side, reduces the
chain-map equation of the full commutation map `GridDiagram.commutationMap` to the four families
of common-side domains, two for each kind of pentagon. The pentagon--rectangle juxtaposition is
described in Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1.

## Main results

* `TauCeti.GridDiagram.pentagonMap_unblockedDifferential_single_eq_iff_overlap`: the
  terminal-side pentagon map commutes with the differentials on a generator exactly when the
  common-side sums agree.
* `TauCeti.GridDiagram.commutationMap_comp_unblockedDifferential_eq_iff_overlap`: the full
  commutation map is a chain map exactly when the common-side sums, for pentagons turning on
  either side, agree.
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)
  (R : Type*) [CommSemiring R] [IsCancelAdd R]

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

open Classical in
/-- The coefficient identity of the commutation chain-map equation, with pentagons turning on
either side, holds exactly when it holds for the common-side contributions: for each kind of
pentagon, the disjoint-side contributions of the two orders cancel by the commuting-domain
pairing. -/
theorem sum_rectanglePentagonWeight_add_sum_rectangleInitialPentagonWeight_eq_iff_overlap
    (x z : GridState n) :
    (∑ D ∈ G.rectanglePentagonDecompositions C x z, G.rectanglePentagonWeight C R D) +
          ∑ D ∈ G.rectangleInitialPentagonDecompositions C x z,
            G.rectangleInitialPentagonWeight C R D =
        (∑ D ∈ G.pentagonRectangleDecompositions C x z, G.pentagonRectangleWeight C R D) +
          ∑ D ∈ G.initialPentagonRectangleDecompositions C x z,
            G.initialPentagonRectangleWeight C R D ↔
      (∑ D ∈ (G.rectanglePentagonDecompositions C x z).filter
          (fun D => ¬ D.HasDisjointSides), G.rectanglePentagonWeight C R D) +
          ∑ D ∈ (G.rectangleInitialPentagonDecompositions C x z).filter
            (fun D => ¬ D.toGridRectangleDecomposition.HasDisjointSides),
            G.rectangleInitialPentagonWeight C R D =
        (∑ D ∈ (G.pentagonRectangleDecompositions C x z).filter
          (fun D => ¬ D.HasDisjointSides), G.pentagonRectangleWeight C R D) +
          ∑ D ∈ (G.initialPentagonRectangleDecompositions C x z).filter
            (fun D => ¬ D.toGridRectangleDecomposition.HasDisjointSides),
            G.initialPentagonRectangleWeight C R D := by
  classical
  have hcancel : ∀ a b c d e f : MvPolynomial (Fin n) R,
      a + b + (c + d) = a + e + (c + f) ↔ b + d = e + f := fun a b c d e f => by
    rw [add_add_add_comm, add_add_add_comm a e, add_right_inj]
  rw [← Finset.sum_filter_add_sum_filter_not
      (G.rectanglePentagonDecompositions C x z) (fun D => D.HasDisjointSides),
    ← Finset.sum_filter_add_sum_filter_not
      (G.pentagonRectangleDecompositions C x z) (fun D => D.HasDisjointSides),
    ← Finset.sum_filter_add_sum_filter_not (G.rectangleInitialPentagonDecompositions C x z)
      (fun D => D.toGridRectangleDecomposition.HasDisjointSides),
    ← Finset.sum_filter_add_sum_filter_not (G.initialPentagonRectangleDecompositions C x z)
      (fun D => D.toGridRectangleDecomposition.HasDisjointSides),
    G.sum_rectanglePentagonWeight_disjoint_eq_sum_pentagonRectangleWeight_disjoint C R x z,
    G.sum_rectangleInitialPentagonWeight_disjoint_eq_sum_initialPentagonRectangleWeight_disjoint
      C R x z]
  exact hcancel _ _ _ _ _ _

open Classical in
/-- The commutation map commutes with the unblocked differentials exactly when, for all grid
states `x` and `z`, the counted common-side rectangle--pentagon and pentagon--rectangle
decompositions from `x` to `z`, with pentagons turning on either side, have the same total
weight. -/
theorem commutationMap_comp_unblockedDifferential_eq_iff_overlap :
    (G.commutationMap R C).comp (G.unblockedDifferential R) =
        ((G.swapColumns C.column (finRotate n C.column)).unblockedDifferential R).comp
          (G.commutationMap R C) ↔
      ∀ x z : GridState n,
        (∑ D ∈ (G.rectanglePentagonDecompositions C x z).filter
            (fun D => ¬ D.HasDisjointSides), G.rectanglePentagonWeight C R D) +
            ∑ D ∈ (G.rectangleInitialPentagonDecompositions C x z).filter
              (fun D => ¬ D.toGridRectangleDecomposition.HasDisjointSides),
              G.rectangleInitialPentagonWeight C R D =
          (∑ D ∈ (G.pentagonRectangleDecompositions C x z).filter
            (fun D => ¬ D.HasDisjointSides), G.pentagonRectangleWeight C R D) +
            ∑ D ∈ (G.initialPentagonRectangleDecompositions C x z).filter
              (fun D => ¬ D.toGridRectangleDecomposition.HasDisjointSides),
              G.initialPentagonRectangleWeight C R D := by
  rw [G.commutationMap_comp_unblockedDifferential_eq_iff C R]
  exact forall_congr' fun x => forall_congr' fun z =>
    G.sum_rectanglePentagonWeight_add_sum_rectangleInitialPentagonWeight_eq_iff_overlap C R x z

end TauCeti.GridDiagram
