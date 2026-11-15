/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Tau
public import TauCeti.KnotTheory.Grid.CrossingChange.UnknottingNumber
public import TauCeti.KnotTheory.Grid.Move.Tau

/-!
# The crossing change and unknotting-number bounds for `τ`

Combining grid-move invariance of `τ` (`GridLink.IsKnot.tau`) with the cross-commutation bound on
knot diagrams (`GridDiagram.IsCrossCommutation.natAbs_tau_sub_le_one`) shows that a single crossing
change between grid knots changes `τ` by at most `1`
(`GridLink.IsCrossingChange.natAbs_tau_sub_le_one`). Inducting along a walk in the crossing change
graph bounds `|τ(L) - τ(L')|` by the extended graph distance `crossingChangeGraph.edist L L'`
(`GridLink.IsKnot.natAbs_tau_sub_le_crossingChangeGraph_edist`), over any commutative ring of
characteristic two.

Over a field of characteristic two, the unknot has `τ = 0` (`GridLink.tau_unknot`). Specializing
the distance bound to `L' = unknot` yields the unknotting-number inequality `|τ(L)| ≤ u(L)`
(`GridLink.IsKnot.natAbs_tau_le_unknottingNumber`).

All statements here are for grid knots (`GridLink.IsKnot`) and the grid-link unknotting number
(`GridLink.unknottingNumber`), defined as crossing-change distance from `unknot` modulo grid moves;
no topological identification with classical embedded knots or concordance invariance is claimed.

## Main results

* `TauCeti.GridLink.IsCrossingChange.natAbs_tau_sub_le_one`: a crossing change between grid knots
  changes `τ` by at most `1`.
* `TauCeti.GridLink.IsKnot.natAbs_tau_sub_le_crossingChangeGraph_edist`: `|τ(L) - τ(L')|` is at
  most the distance between `L` and `L'` in the crossing change graph.
* `TauCeti.GridLink.IsKnot.natAbs_tau_le_unknottingNumber` and
  `TauCeti.GridDiagram.IsKnot.natAbs_tau_le_unknottingNumber_toGridLink`: **the unknotting-number
  bound** `|τ(L)| ≤ u(L)` over any field of characteristic two.
* `TauCeti.GridLink.IsKnot.natAbs_tau_le_of_unknottingNumber_le` and
  `TauCeti.GridLink.IsKnot.tau_mem_Icc_of_unknottingNumber_le`: finite unknotting-number bounds on
  `τ`.
* `TauCeti.GridLink.IsKnot.one_le_unknottingNumber_of_tau_ne_zero` and
  `TauCeti.GridLink.IsKnot.ne_unknot_of_tau_ne_zero`: a grid knot with `τ ≠ 0` is nontrivial.

## References

* P. Ozsváth, Z. Szabó, *Knot Floer homology and the four-ball genus*, Geom. Topol. 7 (2003),
  615--639: the original unknotting-number bound `|τ(K)| ≤ u(K)`.
* S. Sarkar, *Grid diagrams and the Ozsváth--Szabó tau-invariant*, Math. Res. Lett. 18 (2011),
  1239--1257, arXiv:1011.5265: combinatorial proof from grid diagrams.
* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Sections 6.1 and 6.2.
-/

public section

namespace TauCeti

namespace GridLink

/-- A crossing change between two grid knots changes `τ` by at most one, over any commutative ring
of characteristic two. -/
theorem IsCrossingChange.natAbs_tau_sub_le_one {L L' : GridLink} (h : IsCrossingChange L L')
    (hL : L.IsKnot) (hL' : L'.IsKnot) (K : Type*) [CommRing K] [CharP K 2] :
    (hL'.tau K - hL.tau K).natAbs ≤ 1 := by
  obtain ⟨n, G, G', hG, rfl, rfl⟩ := (isCrossingChange_iff L L').mp h
  rw [IsKnot.tau_toGridLink, IsKnot.tau_toGridLink]
  exact hG.natAbs_tau_sub_le_one ((isKnot_toGridLink G).mp hL) ((isKnot_toGridLink G').mp hL') K

/-- Along a walk in the crossing change graph starting and ending at grid knots, `τ` changes by at
most the length of the walk. -/
private theorem natAbs_tau_sub_le_walk_length {L L' : GridLink}
    (w : crossingChangeGraph.Walk L L') (hL : L.IsKnot) (hL' : L'.IsKnot)
    (K : Type*) [CommRing K] [CharP K 2] :
    (hL.tau K - hL'.tau K).natAbs ≤ w.length := by
  induction w with
  | nil => simp
  | @cons u v _ hadj w ih =>
    have hv : v.IsKnot := (crossingChangeGraph_adj.mp hadj).2.isKnot_iff.mpr hL
    have hstep := (crossingChangeGraph_adj.mp hadj).2.natAbs_tau_sub_le_one hL hv K
    have hrest := ih hv hL'
    simp only [SimpleGraph.Walk.length_cons]
    omega

namespace IsKnot

/-- **The crossing-change distance bound for `τ`.** For any two grid knots `L` and `L'`, the
difference `|τ(L) - τ(L')|` is bounded by their extended distance in `crossingChangeGraph`, over
any commutative ring of characteristic two. -/
theorem natAbs_tau_sub_le_crossingChangeGraph_edist {L L' : GridLink}
    (hL : L.IsKnot) (hL' : L'.IsKnot) (K : Type*) [CommRing K] [CharP K 2] :
    (((hL.tau K - hL'.tau K).natAbs : ℕ) : ℕ∞) ≤ crossingChangeGraph.edist L L' := by
  rw [SimpleGraph.edist_eq_sInf]
  refine le_sInf ?_
  rintro _ ⟨w, rfl⟩
  exact Nat.cast_le.mpr (natAbs_tau_sub_le_walk_length w hL hL' K)

/-- **The unknotting-number bound `|τ(L)| ≤ u(L)` for grid knots.** Over any field of
characteristic two, the absolute value of `τ` of a grid knot is at most its unknotting number. -/
theorem natAbs_tau_le_unknottingNumber {L : GridLink} (hL : L.IsKnot)
    (K : Type*) [Field K] [CharP K 2] :
    (((hL.tau K).natAbs : ℕ) : ℕ∞) ≤ L.unknottingNumber := by
  simpa [unknottingNumber_def, tau_unknot] using
    hL.natAbs_tau_sub_le_crossingChangeGraph_edist isKnot_unknot K

/-- If a grid knot can be unknotted in at most `m` crossing changes, then `|τ(L)| ≤ m`. -/
theorem natAbs_tau_le_of_unknottingNumber_le {L : GridLink} (hL : L.IsKnot)
    (K : Type*) [Field K] [CharP K 2] {m : ℕ} (hu : L.unknottingNumber ≤ m) :
    (hL.tau K).natAbs ≤ m :=
  Nat.cast_le.mp ((hL.natAbs_tau_le_unknottingNumber K).trans hu)

/-- If a grid knot can be unknotted in at most `m` crossing changes, then `-m ≤ τ(L) ≤ m`. -/
theorem tau_mem_Icc_of_unknottingNumber_le {L : GridLink} (hL : L.IsKnot)
    (K : Type*) [Field K] [CharP K 2] {m : ℕ} (hu : L.unknottingNumber ≤ m) :
    hL.tau K ∈ Set.Icc (-(m : ℤ)) m := by
  have h := hL.natAbs_tau_le_of_unknottingNumber_le K hu
  exact ⟨by omega, by omega⟩

/-- A grid knot with non-zero `τ` over a field of characteristic two requires at least one crossing
change to unknot. -/
theorem one_le_unknottingNumber_of_tau_ne_zero {L : GridLink} (hL : L.IsKnot)
    {K : Type*} [Field K] [CharP K 2] (h : hL.tau K ≠ 0) :
    1 ≤ L.unknottingNumber :=
  calc (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) := rfl
    _ ≤ (((hL.tau K).natAbs : ℕ) : ℕ∞) := Nat.cast_le.mpr (Int.natAbs_pos.mpr h)
    _ ≤ L.unknottingNumber := hL.natAbs_tau_le_unknottingNumber K

/-- A grid knot with non-zero `τ` over a field of characteristic two is not the unknot. -/
theorem ne_unknot_of_tau_ne_zero {L : GridLink} (hL : L.IsKnot)
    {K : Type*} [Field K] [CharP K 2] (h : hL.tau K ≠ 0) :
    L ≠ unknot := by
  rintro rfl
  exact h (tau_unknot K)

end IsKnot

end GridLink

namespace GridDiagram.IsKnot

/-- On any knot grid diagram, `|τ(G)|` is bounded by the unknotting number of the presented grid
link, over any field of characteristic two. -/
theorem natAbs_tau_le_unknottingNumber_toGridLink {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot)
    (K : Type*) [Field K] [CharP K 2] :
    (((hG.tau K).natAbs : ℕ) : ℕ∞) ≤ G.toGridLink.unknottingNumber := by
  simpa [GridLink.IsKnot.tau_toGridLink] using
    ((GridLink.isKnot_toGridLink G).mpr hG).natAbs_tau_le_unknottingNumber K

end GridDiagram.IsKnot

end TauCeti
