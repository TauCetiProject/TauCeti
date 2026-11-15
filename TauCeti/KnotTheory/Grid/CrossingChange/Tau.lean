/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Grading
public import TauCeti.KnotTheory.Grid.CrossingChange.UnknottingNumber
public import TauCeti.KnotTheory.Grid.Homology.Commutation.Tau
public import TauCeti.KnotTheory.Grid.Move.Tau
import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Equation

/-!
# Crossing change maps and the invariant `τ`

Let `C` be a column turn at the columns `a = C.column` and `b = finRotate n a` of a grid diagram
`G`, and let `G' = G.swapColumns a b`. Write `Φ : GC⁻(G) → GC⁻(G')` for the commutation map of
`C` and `Ψ : GC⁻(G') → GC⁻(G)` for the commutation map of `G'` turning at the same columns in
another row `t`; the target of `Ψ` is the complex of `G'.swapColumns a b`, which is `G`. This file
turns the chain homotopies of the crossing change maps into the crossing change inequality for `τ`.

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
`τ(G) ≤ τ(G') ≤ τ(G) + 1`. In either case `τ` changes by at most one. A row cross-commutation is
a column cross-commutation of the diagonal reflections, which preserve `τ`, so `τ` changes by at
most one across every cross-commutation.

On grid links this says that `τ` changes by at most one across a crossing change. Summing along a
shortest path in the crossing change graph, `|τ(L) - τ(L')|` is at most the number of crossing
changes needed to pass from `L` to `L'`. Since the unknot has `τ = 0`, this gives
`|τ(K)| ≤ u(K)`: the unknotting number of a grid knot is at least `|τ|`. With the values of `τ` on
torus knots, this is the lower bound of the Milnor conjecture.

## Main results

* `TauCeti.GridDiagram.IsKnot.tau_swapColumns_mem_Icc_of_mem_columnArc`: **the crossing change
  inequality**, `τ(G) - 1 ≤ τ(G') ≤ τ(G)` across every crossing change with `O_a` on the arc of
  column `b`.
* `TauCeti.GridDiagram.IsKnot.tau_swapColumns_mem_Icc_of_notMem_columnArc`:
  `τ(G) ≤ τ(G') ≤ τ(G) + 1` across every crossing change with `O_a` off the arc of column `b`.
* `TauCeti.GridDiagram.IsKnot.abs_tau_swapColumns_sub_tau_le_one`: `|τ(G') - τ(G)| ≤ 1` across
  every crossing change.
* `TauCeti.GridDiagram.IsCrossCommutation.abs_tau_sub_tau_le_one`: `|τ(G') - τ(G)| ≤ 1` across
  every cross-commutation, of rows or of columns.
* `TauCeti.GridLink.IsCrossingChange.abs_tau_sub_tau_le_one`: `τ` changes by at most one across a
  crossing change of grid knots.
* `TauCeti.GridLink.IsKnot.natAbs_tau_sub_tau_le_edist`: `|τ(L) - τ(L')|` is at most the
  crossing change distance from `L` to `L'`.
* `TauCeti.GridLink.IsKnot.natAbs_tau_le_unknottingNumber`: **`|τ(K)| ≤ u(K)`**, the unknotting
  number of a grid knot bounds `|τ|`.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Sections 6.1 and 6.2: the crossing change maps, their composites, and
  the resulting inequality for `τ`.
* S. Sarkar, *Grid diagrams and the Ozsváth--Szabó tau-invariant*, Math. Res. Lett. 18 (2011),
  arXiv:1011.5265: the crossing change inequality for `τ` from grid diagrams.
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

variable {n : ℕ} {G G' : GridDiagram n} (K : Type*) [CommRing K] [CharP K 2]

/-- **The crossing change inequality for `τ`**, for every cross-commutation: if the knot grids `G`
and `G'` differ by exchanging two adjacent interleaving columns or rows, then `τ` changes by at
most one, over every commutative ring of characteristic two. A row cross-commutation is a column
cross-commutation of the diagonal reflections, and the reflection preserves `τ`. -/
theorem IsCrossCommutation.abs_tau_sub_tau_le_one (h : G.IsCrossCommutation G') (hG : G.IsKnot)
    (hG' : G'.IsKnot) : |hG'.tau K - hG.tau K| ≤ 1 := by
  rcases (isCrossCommutation_iff G G').mp h with h | h
  · obtain ⟨a, ha, rfl⟩ := (isRowCrossCommutation_iff G G').mp h
    -- Transport the column inequality along the diagonal reflection, which preserves `τ`.
    have hT := G.isKnot_transpose.mpr hG
    have key := hT.abs_tau_swapColumns_sub_tau_le_one K
      ((columnsInterleaving_transpose G _ _).mpr ha)
    rwa [← (hG.unblockedHomologyIsomorphic_transpose K).tau_eq,
      ← (hG'.unblockedHomologyIsomorphic_transpose K).tau_eq.trans
        (IsKnot.tau_eq_of_eq _ K (swapRows_transpose G _ _))] at key
  · obtain ⟨a, ha, rfl⟩ := (isColumnCrossCommutation_iff G G').mp h
    exact hG.abs_tau_swapColumns_sub_tau_le_one K ha

end GridDiagram

namespace GridLink

section CommRing

variable (K : Type*) [CommRing K] [CharP K 2]

/-- **The crossing change inequality for `τ` of grid knots**: if the grid knots `L` and `L'`
differ by a crossing change, then `|τ(L') - τ(L)| ≤ 1`, over every commutative ring of
characteristic two. -/
theorem IsCrossingChange.abs_tau_sub_tau_le_one {L L' : GridLink} (h : L.IsCrossingChange L')
    (hL : L.IsKnot) (hL' : L'.IsKnot) : |hL'.tau K - hL.tau K| ≤ 1 := by
  obtain ⟨n, G, G', hGG', rfl, rfl⟩ := (isCrossingChange_iff L L').mp h
  rw [IsKnot.tau_toGridLink, IsKnot.tau_toGridLink]
  exact hGG'.abs_tau_sub_tau_le_one K _ _

/-- Along a walk of crossing changes between grid knots, `τ` changes by at most the length of the
walk. -/
private theorem natAbs_tau_sub_tau_le_length {L L' : GridLink} (p : crossingChangeGraph.Walk L L')
    (hL : L.IsKnot) (hL' : L'.IsKnot) : (hL'.tau K - hL.tau K).natAbs ≤ p.length := by
  induction p with
  | nil => simp
  | @cons L M L' hadj p ih =>
    have hM : M.IsKnot := by
      rw [isKnot_def, (crossingChangeGraph_adj.mp hadj).2.componentCount_eq, ← isKnot_def]
      exact hL
    have h₁ := (crossingChangeGraph_adj.mp hadj).2.abs_tau_sub_tau_le_one K hL hM
    have h₂ := ih hM hL'
    rw [abs_le] at h₁
    rw [SimpleGraph.Walk.length_cons]
    omega

/-- **`τ` is `1`-Lipschitz for the crossing change distance**: for grid knots `L` and `L'`,
`|τ(L') - τ(L)|` is at most the least number of crossing changes turning `L` into `L'`, over every
commutative ring of characteristic two. -/
theorem IsKnot.natAbs_tau_sub_tau_le_edist {L L' : GridLink} (hL : L.IsKnot) (hL' : L'.IsKnot) :
    ((hL'.tau K - hL.tau K).natAbs : ℕ∞) ≤ crossingChangeGraph.edist L L' := by
  by_cases h : crossingChangeGraph.edist L L' = ⊤
  · simp [h]
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top h
  rw [← hp]
  exact_mod_cast natAbs_tau_sub_tau_le_length K p hL hL'

end CommRing

/-- **The unknotting number bounds `τ`**: a grid knot `L` has `|τ(L)| ≤ u(L)`, over every field of
characteristic two. This is the inequality from which the lower bound of the Milnor conjecture
follows. -/
theorem IsKnot.natAbs_tau_le_unknottingNumber (K : Type*) [Field K] [CharP K 2] {L : GridLink}
    (hL : L.IsKnot) : ((hL.tau K).natAbs : ℕ∞) ≤ L.unknottingNumber := by
  simpa [unknottingNumber_def] using hL.natAbs_tau_sub_tau_le_edist K isKnot_unknot

end GridLink

end TauCeti
