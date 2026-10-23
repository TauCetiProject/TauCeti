/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.Residual.Mixed
public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.Residual.SameSide
public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Overlap.Sum
public import TauCeti.KnotTheory.Grid.Commutation.Overlap.Residual.Assembly
import TauCeti.KnotTheory.Grid.Commutation.Overlap.Partners
import TauCeti.Algebra.CharP.Two

/-!
# The grid commutation map is a chain map

Let `C` be a column turn (`GridDiagram.ColumnTurn`) for a grid diagram `G`, write `G'` for the
diagram `G.swapColumns C.column (finRotate n C.column)`, `∂` and `∂'` for the unblocked
differentials of `G` and `G'`, and `Φ` for the commutation map `GridDiagram.commutationMap`,
which counts empty pentagons turning on either side of the replaced grid line. This file proves
the chain-map equation `Φ ∘ ∂ = ∂' ∘ Φ` over every commutative semiring of characteristic two, in
particular over `𝔽₂`.

The terminal-side contributions have already been reduced to the initial-side ones, so it remains
to account for an initial-side pentagon followed by a rectangle of `G'` whose two pieces share a
side column. The same-side such terms are two recut-partner families and the sources of the
initial-side self-pairing; the mixed-side ones are two further recut-partner families, the turn
cuts and the other members of those self-pairs. The self-pairs cancel in characteristic two, so
the total overlap weight is that of the four recut-partner families and the turn cuts. These are
exactly the terms matched, on the other side of the equation, with the rectangle-followed-by-
initial-side-pentagon overlaps, which proves the equation.

## Main results

* `GridDiagram.sum_initialPentagonRectangleWeight_overlap_eq_sum_partners`: off the diagonal,
  the initial-side pentagon--rectangle overlap terms have the total weight of the four
  recut-partner families and the turn cuts.
* `GridDiagram.commutationMap_comp_unblockedDifferential`: the commutation map is a chain map
  between the unblocked grid complexes, at every column turn.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnTurn n) {x z : GridState n}

variable (R : Type*) [CommSemiring R] [CharP R 2]

open scoped Classical in
/-- Off the diagonal, the initial-side pentagon--rectangle overlap sum is the total weight of the
four recut-partner families and the turn cuts. The remaining same-side and mixed-side terms form
initial-side self-pairs and cancel in characteristic two. -/
theorem sum_initialPentagonRectangleWeight_overlap_eq_sum_partners (hzx : z ≠ x) :
    ∑ E ∈ (G.initialPentagonRectangleDecompositions C x z).filter
          (fun E => ¬E.toGridRectangleDecomposition.HasDisjointSides),
        G.initialPentagonRectangleWeight C R E =
      (∑ E ∈ G.initialPentagonInitialCrossOverlapPartners C x z,
          G.initialPentagonRectangleWeight C R E) +
        (∑ E ∈ G.initialPentagonTerminalOverlapPartners C x z,
          G.initialPentagonRectangleWeight C R E) +
          (∑ E ∈ G.initialPentagonLeftRightOverlapPartners C x z,
            G.initialPentagonRectangleWeight C R E) +
            (∑ E ∈ G.initialPentagonRightLeftOverlapPartners C x z,
              G.initialPentagonRectangleWeight C R E) +
              ∑ E ∈ G.initialPentagonRectangleTurnCuts C x z,
                G.initialPentagonRectangleWeight C R E := by
  rw [sum_initialPentagonRectangle_overlap_eq_sameSide_add_mixedSide C
      (G.initialPentagonRectangleDecompositions C x z) (G.initialPentagonRectangleWeight C R) hzx,
    G.sum_initialPentagonRectangle_sameSide_eq_sum_partners_add_sum_selfSources C,
    G.sum_initialPentagonRectangle_mixedSide_eq_sum_partners_add_turnCuts_add_selfPairs C
      (G.initialPentagonRectangleWeight C R) hzx]
  have hself := G.sum_initialPentagonRectangleInitialSelfPairs_eq_sum_sources_add_sum_mixed C
    (x := x) (z := z) (G.initialPentagonRectangleWeight C R)
  rw [G.sum_initialPentagonRectangleWeight_initialSelfPairs_eq_zero C R x z] at hself
  -- The four partner sums and the turn-cut sum occur on both sides; the residual self-pair
  -- contributions vanish together, even though neither orientation need vanish separately.
  calc
    _ = ((∑ E ∈ G.initialPentagonInitialCrossOverlapPartners C x z,
            G.initialPentagonRectangleWeight C R E) +
          (∑ E ∈ G.initialPentagonTerminalOverlapPartners C x z,
            G.initialPentagonRectangleWeight C R E) +
            (∑ E ∈ G.initialPentagonLeftRightOverlapPartners C x z,
              G.initialPentagonRectangleWeight C R E) +
              (∑ E ∈ G.initialPentagonRightLeftOverlapPartners C x z,
                G.initialPentagonRectangleWeight C R E) +
                ∑ E ∈ G.initialPentagonRectangleTurnCuts C x z,
                  G.initialPentagonRectangleWeight C R E) +
        ((∑ E ∈ G.initialPentagonRectangleInitialSelfSources C x z,
            G.initialPentagonRectangleWeight C R E) +
          ∑ E ∈ (G.initialPentagonRectangleInitialSelfPairs C x z).filter
            (fun E => E.toGridRectangleDecomposition.HasMixedSideOverlap),
            G.initialPentagonRectangleWeight C R E) := by
      ac_rfl
    _ = _ := by rw [← hself, add_zero]

/-- **The commutation map is a chain map.** Over a commutative semiring of characteristic two,
counting empty pentagons turning on either side of the replaced grid line intertwines the unblocked
differentials of a grid diagram and of the diagram with the two columns of the turn exchanged.
This holds at every column turn: the two marking segments need not be non-interleaving. -/
theorem commutationMap_comp_unblockedDifferential :
    (G.commutationMap R C).comp (G.unblockedDifferential R) =
      ((G.swapColumns C.column (finRotate n C.column)).unblockedDifferential R).comp
        (G.commutationMap R C) := by
  classical
  refine (G.commutationMap_comp_unblockedDifferential_eq_iff_sdiff_crossOverlapPartners C R).2
    fun x z hzx => ?_
  have hterminal := G.sum_pentagonRectangleWeight_overlap_eq_sum_partners C R hzx
  rw [← G.sum_crossOverlapPartners C (G.pentagonRectangleWeight C R) hzx,
    ← Finset.sum_sdiff (G.crossOverlapPartners_subset_filter C hzx)
      (f := G.pentagonRectangleWeight C R)] at hterminal
  have hinitial := G.sum_initialPentagonRectangleWeight_overlap_eq_sum_partners C R hzx
  rw [← G.sum_initialPentagonCrossOverlapPartners C (G.initialPentagonRectangleWeight C R) hzx,
    ← Finset.sum_sdiff (G.initialPentagonCrossOverlapPartners_subset_filter C hzx)
      (f := G.initialPentagonRectangleWeight C R)] at hinitial
  -- Remove each disjoint recut-partner union once, leaving exactly the turn cuts.
  have := isCancelAdd_of_charTwo R
  exact congrArg₂ (· + ·)
    (add_right_cancel (hterminal.trans (add_comm _ _)))
    (add_right_cancel (hinitial.trans (add_comm _ _)))

end TauCeti.GridDiagram
