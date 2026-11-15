/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.UnknottingNumber
public import TauCeti.KnotTheory.Grid.Move.Tau
import TauCeti.KnotTheory.Grid.CrossingChange.Grading
import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Equation
import TauCeti.KnotTheory.Grid.Homology.Commutation.Tau

/-!
# Crossing change maps, the invariant `τ`, and the unknotting-number bound

Let `C` be a column turn at the columns `a = C.column` and `b = finRotate n a` of a grid diagram
`G`, and let `G' = G.swapColumns a b`. Write `Φ : GC⁻(G) → GC⁻(G')` for the commutation map of
`C` and `Ψ : GC⁻(G') → GC⁻(G)` for the commutation map of `G'` turning at the same columns in
another row `t`; the target of `Ψ` is the complex of `G'.swapColumns a b`, which is `G`. This file
turns the chain homotopies of the crossing change maps into the crossing change inequality for `τ`
and deduces the bound `|τ(L)| ≤ u(L)` by the unknotting number.

The comparison along a single column turn is in `Homology/Commutation/Tau.lean`: if
`ΨΦ` is chain homotopic to multiplication by `p` with `p(U, …, U) = U ^ k`, then `GH⁻(G')` is not
torsion if `GH⁻(G)` is not (`GridDiagram.IsKnot.not_isTorsion_swapColumns_of_homotopy`), and
`τ(G')` is at most `τ(G)` minus the Alexander degree of `Φ`
(`GridDiagram.IsKnot.tau_swapColumns_le_of_homotopy`).

The main application is to a crossing change. If the segments of the columns `a` and `b`
interleave with `O_a` on the arc of column `b`, the crossing change maps are the commutation map
`Φ` turning in the row of `O_a`, of Alexander degree `0`, and the commutation map `Ψ` of `G'`
turning in the row of `X_b`, of Alexander degree `-1`
(`GridDiagram.commutationBidegree_eq_zero_of_mem_columnArc` and
`GridDiagram.commutationBidegree_eq_of_notMem_columnArc`). Ozsváth, Stipsicz and Szabó show that
both composites are chain homotopic to multiplication by a variable, `ΨΦ` to `V_b` and `ΦΨ` to
`V_a`, with the hexagon-counting maps `GridDiagram.crossingChangeHomotopy` as the homotopies; these
homotopy equations are in `CrossingChange/Homotopy/Equation.lean`. Together they give
`τ(G) - 1 ≤ τ(G') ≤ τ(G)` (`GridDiagram.IsKnot.tau_swapColumns_mem_Icc_of_mem_columnArc`). No
assumption that `GH⁻` is non-torsion is needed here: the two composites show that `GH⁻(G)` and
`GH⁻(G')` are torsion together, and then both invariants vanish. With `O_a` off the arc of column
`b`, the markings of `G'` are in the first order and exchanging its columns returns `G`, so
`τ(G) ≤ τ(G') ≤ τ(G) + 1`. In either case `τ` changes by at most one.

Diagonal reflection extends the bound `|τ(G') - τ(G)| ≤ 1` from column cross-commutations to row
cross-commutations and hence to every crossing change of grid knots
(`GridLink.IsCrossingChange.natAbs_tau_sub_le_one`). Induction along walks in
`GridLink.crossingChangeGraph` then shows that `|τ(L) - τ(L')|` is bounded by the crossing-change
distance (`GridLink.IsKnot.natAbs_tau_sub_le_edist`), and specializing `L'` to the unknot over a
field of characteristic two yields `|τ(L)| ≤ u(L)`
(`GridLink.IsKnot.natAbs_tau_le_unknottingNumber`).

## Main results

* `TauCeti.GridDiagram.IsKnot.tau_swapColumns_mem_Icc_of_mem_columnArc`: **the crossing change
  inequality**, `τ(G) - 1 ≤ τ(G') ≤ τ(G)` across every crossing change with `O_a` on the arc of
  column `b`.
* `TauCeti.GridDiagram.IsKnot.tau_swapColumns_mem_Icc_of_notMem_columnArc`:
  `τ(G) ≤ τ(G') ≤ τ(G) + 1` across every crossing change with `O_a` off the arc of column `b`.
* `TauCeti.GridDiagram.IsKnot.abs_tau_swapColumns_sub_tau_le_one`: `|τ(G') - τ(G)| ≤ 1` across
  every crossing change.
* `TauCeti.GridDiagram.IsCrossCommutation.natAbs_tau_sub_le_one` and
  `TauCeti.GridLink.IsCrossingChange.natAbs_tau_sub_le_one`: a single cross-commutation or crossing
  change alters `τ` by at most `1`.
* `TauCeti.GridLink.IsKnot.natAbs_tau_sub_le_edist`: `|τ(L) - τ(L')|` is bounded by the extended
  distance in `crossingChangeGraph`.
* `TauCeti.GridLink.IsKnot.natAbs_tau_le_unknottingNumber`: **the unknotting-number bound**
  `|τ(L)| ≤ u(L)` over any field of characteristic two.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Sections 6.1 and 6.2: the crossing change maps, their composites, and
  the resulting crossing-change and unknotting-number bounds for `τ`.
* S. Sarkar, *Grid diagrams and the Ozsváth--Szabó tau-invariant*, Math. Res. Lett. 18 (2011),
  arXiv:1011.5265: the crossing-change inequality and unknotting-number bound for `τ` from grid
  diagrams.
-/

public section

open MvPolynomial

namespace TauCeti

namespace GridDiagram

namespace IsKnot

variable {n : ℕ} {G : GridDiagram n} (hG : G.IsKnot) (K : Type*) [CommRing K] [CharP K 2]

/-- **The crossing change inequality for `τ`.** Let the segments of the columns `a` and
`b = finRotate n a` of a knot grid `G` interleave with `O_a` on the arc of column `b`. Then
`τ(G) - 1 ≤ τ(G') ≤ τ(G)` for `G' = G.swapColumns a b`, over every commutative ring of
characteristic two.

The crossing change maps are the commutation map `Φ` turning in the row of `O_a` and the
commutation map `Ψ` of `G'` turning in the row of `X_b`. Their composites `ΨΦ` and `ΦΨ` are chain
homotopic to multiplication by `V_b` and `V_a`, which bounds `τ` in both directions. -/
theorem tau_swapColumns_mem_Icc_of_mem_columnArc {a : Fin n}
    (h : G.ColumnsInterleaving a (finRotate n a)) (hO : G.O a ∈ G.columnArc (finRotate n a)) :
    (hG.swapColumns a (finRotate n a)).tau K ∈ Set.Icc (hG.tau K - 1) (hG.tau K) := by
  let C : ColumnTurn n := ⟨a, G.O a, h.ne⟩
  let _ := hG.unblockedHomologyModule K
  let _ := (hG.swapColumns a (finRotate n a)).unblockedHomologyModule K
  let _ := ((hG.swapColumns a (finRotate n a)).swapColumns a
    (finRotate n a)).unblockedHomologyModule K
  have hp (c : Fin n) :
      aeval (fun _ => (Polynomial.X : Polynomial K)) (MvPolynomial.X c : MvPolynomial (Fin n) K) =
        Polynomial.X ^ 1 := by
    rw [aeval_X, pow_one]
  -- In `G'` the markings of the exchanged columns appear in the other cyclic order.
  have h' := (columnsInterleaving_swapColumns G _ _).mpr h.symm
  have hO' : (G.swapColumns a (finRotate n a)).O a ∉
      (G.swapColumns a (finRotate n a)).columnArc (finRotate n a) :=
    fun hO' => h.O_swapColumns_mem_columnArc_iff.mp hO' hO
  have hs' : (C.withTurnRow (G.X (finRotate n a))).turnRow =
      (G.swapColumns a (finRotate n a)).X a := by
    simp [swapColumns_X, GridState.swapColumns_apply]
  have hH := unblockedDifferential_crossingChangeHomotopy_add_eq_of_mem_columnArc (C := C) K h hO
    rfl rfl
  have hH' := unblockedDifferential_crossingChangeHomotopy_add_eq_of_notMem_columnArc
    (C := C.withTurnRow (G.X (finRotate n a))) (t := G.O a) K h' hO' hs'
    (by simp [C, swapColumns_O, GridState.swapColumns_apply])
  -- The commutation map back has the bidegree of multiplication by `U`.
  have hΦ := commutationBidegree_eq_zero_of_mem_columnArc C h hO rfl
  have hΨ := commutationBidegree_eq_of_notMem_columnArc (C.withTurnRow (G.X (finRotate n a))) h'
    hO' hs'
  have hΨ' := (hG.swapColumns a (finRotate n a)).not_isTorsion_swapColumns_of_homotopy K
    (C.withTurnRow (G.X (finRotate n a))) (G.O a) _ (hp a) hH'
  by_cases hT : Module.IsTorsion (Polynomial K) (G.unblockedHomology K)
  · -- Both homologies are torsion, and both invariants vanish.
    have hT' : Module.IsTorsion (Polynomial K)
        ((G.swapColumns a (finRotate n a)).unblockedHomology K) := by
      by_contra hT'
      exact (hΨ' hT') ((hG.isTorsion_unblockedHomology_swapColumns_swapColumns_iff K _ _).mpr hT)
    rw [hG.tau_eq_zero_of_isTorsion K hT,
      (hG.swapColumns a (finRotate n a)).tau_eq_zero_of_isTorsion K hT']
    simp
  · have h₁ := hG.tau_swapColumns_le_of_homotopy K C (G.X (finRotate n a)) _ (hp _) hH hT
    have h₂ := (hG.swapColumns a (finRotate n a)).tau_swapColumns_le_of_homotopy K
      (C.withTurnRow (G.X (finRotate n a))) (G.O a) _ (hp a) hH'
      (hG.not_isTorsion_swapColumns_of_homotopy K C (G.X (finRotate n a)) _ (hp _) hH hT)
    rw [hΦ, Prod.snd_zero, sub_zero] at h₁
    rw [hΨ, hG.tau_swapColumns_swapColumns, sub_neg_eq_add] at h₂
    exact ⟨by linarith, h₁⟩

/-- **The crossing change inequality for `τ`**, for the other crossing sign. Let the segments of
the columns `a` and `b = finRotate n a` of a knot grid `G` interleave with `O_a` off the arc of
column `b`. Then `τ(G) ≤ τ(G') ≤ τ(G) + 1` for `G' = G.swapColumns a b`, over every commutative
ring of characteristic two. -/
theorem tau_swapColumns_mem_Icc_of_notMem_columnArc {a : Fin n}
    (h : G.ColumnsInterleaving a (finRotate n a)) (hO : G.O a ∉ G.columnArc (finRotate n a)) :
    (hG.swapColumns a (finRotate n a)).tau K ∈ Set.Icc (hG.tau K) (hG.tau K + 1) := by
  -- In `G'` the markings of the exchanged columns appear in the other cyclic order, and
  -- exchanging the columns of `G'` again returns `G`.
  have key := (hG.swapColumns a (finRotate n a)).tau_swapColumns_mem_Icc_of_mem_columnArc K
    ((columnsInterleaving_swapColumns G _ _).mpr h.symm) (h.O_swapColumns_mem_columnArc_iff.mpr hO)
  rw [hG.tau_swapColumns_swapColumns] at key
  exact ⟨key.2, by linarith [key.1]⟩

/-- **The crossing change inequality for `τ`**, for either crossing sign: if the segments of the
columns `a` and `b = finRotate n a` of a knot grid `G` interleave, then `τ` changes by at most one
under the crossing change `G' = G.swapColumns a b`, over every commutative ring of characteristic
two. -/
theorem abs_tau_swapColumns_sub_tau_le_one {a : Fin n}
    (h : G.ColumnsInterleaving a (finRotate n a)) :
    |(hG.swapColumns a (finRotate n a)).tau K - hG.tau K| ≤ 1 := by
  rw [abs_sub_le_iff]
  by_cases hO : G.O a ∈ G.columnArc (finRotate n a)
  · have key := hG.tau_swapColumns_mem_Icc_of_mem_columnArc K h hO
    exact ⟨by linarith [key.2], by linarith [key.1]⟩
  · have key := hG.tau_swapColumns_mem_Icc_of_notMem_columnArc K h hO
    exact ⟨by linarith [key.2], by linarith [key.1]⟩

end IsKnot

/-! ### Cross-commutation bounds on knot diagrams -/

/-- A column cross-commutation between knot grid diagrams alters `τ` by at most `1` in absolute
value. -/
theorem IsColumnCrossCommutation.abs_tau_sub_le_one {n : ℕ} {G G' : GridDiagram n}
    (h : G.IsColumnCrossCommutation G') (hG : G.IsKnot) (hG' : G'.IsKnot)
    (K : Type*) [CommRing K] [CharP K 2] :
    |hG'.tau K - hG.tau K| ≤ 1 := by
  obtain ⟨a, ha, rfl⟩ := (isColumnCrossCommutation_iff _ _).mp h
  exact hG.abs_tau_swapColumns_sub_tau_le_one K ha

/-- A column cross-commutation between knot grid diagrams alters `τ` by at most `1`. -/
theorem IsColumnCrossCommutation.natAbs_tau_sub_le_one {n : ℕ} {G G' : GridDiagram n}
    (h : G.IsColumnCrossCommutation G') (hG : G.IsKnot) (hG' : G'.IsKnot)
    (K : Type*) [CommRing K] [CharP K 2] :
    (hG'.tau K - hG.tau K).natAbs ≤ 1 := by
  have habs := h.abs_tau_sub_le_one hG hG' K
  rw [← Int.natCast_natAbs] at habs
  exact Nat.cast_le.mp habs

/-- A row cross-commutation between knot grid diagrams alters `τ` by at most `1`. -/
theorem IsRowCrossCommutation.natAbs_tau_sub_le_one {n : ℕ} {G G' : GridDiagram n}
    (h : G.IsRowCrossCommutation G') (hG : G.IsKnot) (hG' : G'.IsKnot)
    (K : Type*) [CommRing K] [CharP K 2] :
    (hG'.tau K - hG.tau K).natAbs ≤ 1 := by
  simpa only [IsKnot.tau_transpose] using
    ((G.isColumnCrossCommutation_transpose G').mpr h).natAbs_tau_sub_le_one
      ((G.isKnot_transpose).mpr hG) ((G'.isKnot_transpose).mpr hG') K

/-- A row cross-commutation between knot grid diagrams alters `τ` by at most `1` in absolute
value. -/
theorem IsRowCrossCommutation.abs_tau_sub_le_one {n : ℕ} {G G' : GridDiagram n}
    (h : G.IsRowCrossCommutation G') (hG : G.IsKnot) (hG' : G'.IsKnot)
    (K : Type*) [CommRing K] [CharP K 2] :
    |hG'.tau K - hG.tau K| ≤ 1 := by
  rw [← Int.natCast_natAbs]
  exact Nat.cast_le.mpr (h.natAbs_tau_sub_le_one hG hG' K)

/-- Any cross-commutation (of rows or columns) between knot grid diagrams alters `τ` by at most
`1`. -/
theorem IsCrossCommutation.natAbs_tau_sub_le_one {n : ℕ} {G G' : GridDiagram n}
    (h : G.IsCrossCommutation G') (hG : G.IsKnot) (hG' : G'.IsKnot)
    (K : Type*) [CommRing K] [CharP K 2] :
    (hG'.tau K - hG.tau K).natAbs ≤ 1 := by
  rcases (isCrossCommutation_iff _ _).mp h with h | h
  · exact h.natAbs_tau_sub_le_one hG hG' K
  · exact h.natAbs_tau_sub_le_one hG hG' K

/-- Any cross-commutation between knot grid diagrams alters `τ` by at most `1` in absolute value. -/
theorem IsCrossCommutation.abs_tau_sub_le_one {n : ℕ} {G G' : GridDiagram n}
    (h : G.IsCrossCommutation G') (hG : G.IsKnot) (hG' : G'.IsKnot)
    (K : Type*) [CommRing K] [CharP K 2] :
    |hG'.tau K - hG.tau K| ≤ 1 := by
  rw [← Int.natCast_natAbs]
  exact Nat.cast_le.mpr (h.natAbs_tau_sub_le_one hG hG' K)

end GridDiagram

/-! ### Crossing-change distance and the unknotting-number bound on grid knots -/

namespace GridLink

/-- A crossing change between grid knots alters `τ` by at most `1`. -/
theorem IsCrossingChange.natAbs_tau_sub_le_one {L L' : GridLink}
    (h : IsCrossingChange L L') (hL : L.IsKnot) (hL' : L'.IsKnot)
    (K : Type*) [CommRing K] [CharP K 2] :
    (hL'.tau K - hL.tau K).natAbs ≤ 1 := by
  obtain ⟨n, G, G', hcross, rfl, rfl⟩ := (isCrossingChange_iff _ _).mp h
  rw [IsKnot.tau_toGridLink, IsKnot.tau_toGridLink]
  exact hcross.natAbs_tau_sub_le_one _ _ K

/-- A crossing change between grid knots alters `τ` by at most `1` in absolute value. -/
theorem IsCrossingChange.abs_tau_sub_le_one {L L' : GridLink}
    (h : IsCrossingChange L L') (hL : L.IsKnot) (hL' : L'.IsKnot)
    (K : Type*) [CommRing K] [CharP K 2] :
    |hL'.tau K - hL.tau K| ≤ 1 := by
  rw [← Int.natCast_natAbs]
  exact Nat.cast_le.mpr (h.natAbs_tau_sub_le_one hL hL' K)

namespace IsKnot

/-- Along any walk in the crossing-change graph between grid knots, `τ` changes by at most the
length of the walk. -/
theorem natAbs_tau_sub_le_length {L L' : GridLink} (hL : L.IsKnot) (hL' : L'.IsKnot)
    (K : Type*) [CommRing K] [CharP K 2] (p : crossingChangeGraph.Walk L L') :
    (hL'.tau K - hL.tau K).natAbs ≤ p.length := by
  induction p with
  | nil => simp
  | @cons u v w hadj p ih =>
    have hcc : IsCrossingChange u v := (crossingChangeGraph_adj.mp hadj).2
    have hv : v.IsKnot := hcc.isKnot_iff.mpr hL
    have hstep := hcc.natAbs_tau_sub_le_one hL hv K
    have htail := ih hv hL'
    have htri := Int.natAbs_add_le (hL'.tau K - hv.tau K) (hv.tau K - hL.tau K)
    rw [sub_add_sub_cancel] at htri
    simp only [SimpleGraph.Walk.length_cons]
    omega

/-- **Crossing-change distance bound for `τ`.** Between any two grid knots `L` and `L'`, the
difference `|τ(L) - τ(L')|` is bounded by their extended distance in `crossingChangeGraph`. -/
theorem natAbs_tau_sub_le_edist {L L' : GridLink} (hL : L.IsKnot) (hL' : L'.IsKnot)
    (K : Type*) [CommRing K] [CharP K 2] :
    ((hL.tau K - hL'.tau K).natAbs : ℕ∞) ≤ crossingChangeGraph.edist L L' := by
  rw [SimpleGraph.edist_eq_sInf, le_sInf_iff]
  rintro _ ⟨p, rfl⟩
  rw [← Int.natAbs_neg, neg_sub]
  exact Nat.cast_le.mpr (hL.natAbs_tau_sub_le_length hL' K p)

/-- **The unknotting-number bound for `τ`.** For every grid knot `L` and every field `K` of
characteristic two, `|τ(L)| ≤ u(L)`. -/
theorem natAbs_tau_le_unknottingNumber {L : GridLink} (hL : L.IsKnot)
    (K : Type*) [Field K] [CharP K 2] :
    ((hL.tau K).natAbs : ℕ∞) ≤ L.unknottingNumber := by
  simpa only [unknottingNumber_def, tau_unknot, sub_zero] using
    hL.natAbs_tau_sub_le_edist isKnot_unknot K

/-- If a grid knot can be unknotted in at most `m` crossing changes, then `|τ(L)| ≤ m`. -/
theorem abs_tau_le_of_unknottingNumber_le {L : GridLink} (hL : L.IsKnot)
    (K : Type*) [Field K] [CharP K 2] {m : ℕ} (hu : L.unknottingNumber ≤ m) :
    |hL.tau K| ≤ m := by
  rw [← Int.natCast_natAbs]
  exact Nat.cast_le.mpr (Nat.cast_le.mp ((hL.natAbs_tau_le_unknottingNumber K).trans hu))

end IsKnot

end GridLink

end TauCeti
