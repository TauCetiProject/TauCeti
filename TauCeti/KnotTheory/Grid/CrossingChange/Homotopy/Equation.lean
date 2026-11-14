/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Mixed
public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.SameSide
public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Unpaired
import TauCeti.Algebra.BigOperators.Finset.Pairing
import TauCeti.Algebra.CharP.Two

/-!
# The homotopy equation of a crossing change

Let `C` be a column turn at the columns `a = C.column` and `b = finRotate n a` of a grid diagram
`G`, turning in row `s = C.turnRow`, and let `t ≠ s` be a second row such that the annulus squares
`GridDiagram.crossingChangeAnnulusSquares C t` carry no `X`-marking. Write `Φ : GC⁻(G) → GC⁻(G')`
for the commutation map of `C`, where `G' = G.swapColumns a b`, `Ψ : GC⁻(G') → GC⁻(G)` for the
commutation map of `G'` turning in row `t`, `H : GC⁻(G) → GC⁻(G)` for the hexagon-counting map
`GridDiagram.crossingChangeHomotopy`, and `w` for the annulus weight
`GridDiagram.crossingChangeAnnulusWeight`. This file proves the crossing-change homotopy equation

  `∂ ∘ H + H ∘ ∂ = w + Ψ ∘ Φ`

over every commutative semiring of characteristic two.

The diagonal terms (`Homotopy.Diagonal`), the disjoint-side composites (`Homotopy.Disjoint`), and
the recut-paired overlapping composites (`Homotopy.Recut`) reduce the equation to matching, for
distinct grid states `x` and `z`, the unpaired hexagon composites
`GridDiagram.crossingChangeUnpairedHexagonComposites` with the pairs of pentagons counted by
`Ψ ∘ Φ` (`GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_iff_unpaired`). Every
counted same-side pentagon pair recuts to a unique unpaired composite of the same weight
(`Homotopy.SameSide`), every counted mixed-side pentagon pair shares its underlying rectangles and
weight with a unique unpaired composite (`Homotopy.Mixed`), and every unpaired composite arises
from one of the two constructions (`Homotopy.Unpaired`). Because the replaced grid line `b` is a
common side of every mixed-side composite and never a common side of the recut of a same-side
pentagon pair, the two matchings have disjoint images and assemble into a weight-preserving
bijection over any commutative semiring.

For interleaving columns `a` and `b`, the annulus squares carry no `X`-marking and the annulus
weight `w` is a single variable: `V_b` when `O_a` lies on the arc of column `b` and the maps turn
at `O_a` and `X_b`, and `V_a` when `O_a` lies off that arc and the maps turn at `X_a` and `O_b`.

## Main results

* `sum_crossingChangeUnpairedHexagonCompositeWeight_eq_sum_pentagonPairWeight` and
  `sum_crossingChangeUnpairedHexagonCompositeWeight_eq`, in `TauCeti.GridDiagram`: off the
  diagonal, the unpaired crossing-change hexagon composites and the counted pentagon pairs have the
  same total polynomial weight over every commutative semiring.
* `TauCeti.GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq`: **the crossing-change
  homotopy equation** `∂ ∘ H + H ∘ ∂ = w + Ψ ∘ Φ` in characteristic two, together with its
  interleaving specializations `_of_mem_columnArc` (`w = V_b`) and `_of_notMem_columnArc`
  (`w = V_a`), and its cycle corollaries `commutationMap_withTurnRow_commutationMap_of_mem_ker`,
  `_of_mem_columnArc`, and `_of_notMem_columnArc`.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Section 6.1: the crossing-change maps and their hexagon homotopies.
* M. Kendall, *Crossing change maps in filtered grid homology*, arXiv:2303.04227, Section 3: the
  homotopy equations for hexagons with corners at two turn points.

The finite-sum assembly and cycle corollary adapt the commutation-homotopy proof across
`TauCeti.KnotTheory.Grid.Commutation.Homotopy` (`Decomposition`, `SameSideRecut`, `SameSide`,
`Mixed.Side`, and `Equation`), reusing `GridDiagram.pentagonPairDecompositions`,
`GridDiagram.pentagonPairWeight`,
`GridDiagram.sum_rename_commutationPentagonCoefficient_mul_commutationPentagonCoefficient`,
`GridPentagonPairDecomposition.finRotate_mem_commonSideColumns`, and
`GridPentagonPairDecomposition.finRotate_notMem_commonSideColumns_of_sameSide_isRecut`, and
adapting `GridDiagram.sum_pentagonPairWeight_sameSide_eq_sum_partners`,
`GridDiagram.sum_pentagonPairWeight_mixedSide_eq_sum_partners`,
`GridDiagram.disjoint_sameSidePentagonPartners_mixedSidePentagonPartners`,
`GridDiagram.unblockedDifferential_commutationHomotopy_add_eq`, and
`GridDiagram.commutationMap_reverse_commutationMap_of_mem_ker` to two arbitrary turn rows with
non-unit annulus weight.
-/

public section

namespace TauCeti.GridDiagram

open MvPolynomial

variable {n : ℕ} {G : GridDiagram n} {C : ColumnTurn n} {t : Fin n}

local notation "a" => C.column
local notation "b" => finRotate n C.column

/-! ### Matching unpaired composites with pentagon pairs -/

section Matching

/-- Each counted off-diagonal pentagon pair has an unpaired hexagon-composite partner of the same
weight: its recut in the same-side case, or the composite with the same rectangles in the
mixed-side case. -/
private theorem exists_unpairedPartner_of_mem_pentagonPairDecompositions
    (R : Type*) [CommSemiring R] (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) {x z : GridState n} (hzx : z ≠ x)
    {D : GridPentagonPairDecomposition a C.turnRow a t x z}
    (hD : D ∈ G.pentagonPairDecompositions C (C.withTurnRow t) x z) :
    ∃ F ∈ G.crossingChangeUnpairedHexagonComposites C t x z,
      ((D.first.isLeft = D.second.isLeft ∧
          D.toRectangleDecomposition.IsRecut F.toRectangleDecomposition) ∨
        (D.first.isLeft ≠ D.second.isLeft ∧
          D.toRectangleDecomposition = F.toRectangleDecomposition)) ∧
        G.pentagonPairWeight C (C.withTurnRow t) R D =
          G.crossingChangeHexagonCompositeWeight C t R F := by
  obtain ⟨hP, hQ⟩ := (G.mem_pentagonPairDecompositions C (C.withTurnRow t) D).mp hD
  rcases D with ⟨m, P | P, Q | Q⟩
  · obtain ⟨⟨F, ⟨hF, hrecut⟩, -⟩, hw⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_terminalPentagonPair R hX P Q
        ((G.inl_mem_commutationPentagons C P).mp hP)
        (((G.swapColumns a b).inl_mem_commutationPentagons (C.withTurnRow t) Q).mp hQ) hzx
    refine ⟨F, hF, Or.inl ⟨rfl, ?_⟩, ?_⟩
    · simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inl] using hrecut
    · rw [G.pentagonPairWeight_def, G.commutationPentagonWeight_inl,
        (G.swapColumns a b).commutationPentagonWeight_inl]
      exact (hw F hF hrecut).symm
  · obtain ⟨F, ⟨hF, hFD, hw⟩, -⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_terminalInitialPentagonPair R hst hX
        P Q ((G.inl_mem_commutationPentagons C P).mp hP)
        (((G.swapColumns a b).inr_mem_commutationPentagons (C.withTurnRow t) Q).mp hQ) hzx
    refine ⟨F, hF, Or.inr ⟨by simp, ?_⟩, ?_⟩
    · simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inl,
        GridCommutationPentagonBetween.toGridRectangleBetween_inr] using hFD.symm
    · rw [G.pentagonPairWeight_def, G.commutationPentagonWeight_inl,
        (G.swapColumns a b).commutationPentagonWeight_inr]
      exact hw.symm
  · obtain ⟨F, ⟨hF, hFD, hw⟩, -⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_initialTerminalPentagonPair R hst hX
        P Q ((G.inr_mem_commutationPentagons C P).mp hP)
        (((G.swapColumns a b).inl_mem_commutationPentagons (C.withTurnRow t) Q).mp hQ) hzx
    refine ⟨F, hF, Or.inr ⟨by simp, ?_⟩, ?_⟩
    · simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inl,
        GridCommutationPentagonBetween.toGridRectangleBetween_inr] using hFD.symm
    · rw [G.pentagonPairWeight_def, G.commutationPentagonWeight_inr,
        (G.swapColumns a b).commutationPentagonWeight_inl]
      exact hw.symm
  · obtain ⟨⟨F, ⟨hF, hrecut⟩, -⟩, hw⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_initialPentagonPair R hX P Q
        ((G.inr_mem_commutationPentagons C P).mp hP)
        (((G.swapColumns a b).inr_mem_commutationPentagons (C.withTurnRow t) Q).mp hQ) hzx
    refine ⟨F, hF, Or.inl ⟨rfl, ?_⟩, ?_⟩
    · simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inr] using hrecut
    · rw [G.pentagonPairWeight_def, G.commutationPentagonWeight_inr,
        (G.swapColumns a b).commutationPentagonWeight_inr]
      exact (hw F hF hrecut).symm

/-- **Off-diagonal matching for a crossing change.** If the turn rows `C.turnRow` and `t` differ
and the annulus squares carry no `X`-marking, then for distinct grid states `x` and `z` the
unpaired hexagon composites and the counted pentagon pairs have equal total polynomial weight over
every commutative semiring. -/
theorem sum_crossingChangeUnpairedHexagonCompositeWeight_eq_sum_pentagonPairWeight
    (R : Type*) [CommSemiring R] (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) {x z : GridState n} (hxz : x ≠ z) :
    ∑ F ∈ G.crossingChangeUnpairedHexagonComposites C t x z,
        G.crossingChangeHexagonCompositeWeight C t R F =
      ∑ D ∈ G.pentagonPairDecompositions C (C.withTurnRow t) x z,
        G.pentagonPairWeight C (C.withTurnRow t) R D := by
  have hzx : z ≠ x := hxz.symm
  have hcomp {F} (hF : F ∈ G.crossingChangeUnpairedHexagonComposites C t x z) :=
    ((G.mem_crossingChangeUnpairedHexagonComposites C t F).mp hF).1
  symm
  refine Finset.sum_bij_of_rel
    (fun D F =>
      (D.first.isLeft = D.second.isLeft ∧
          D.toRectangleDecomposition.IsRecut F.toRectangleDecomposition) ∨
        (D.first.isLeft ≠ D.second.isLeft ∧
          D.toRectangleDecomposition = F.toRectangleDecomposition))
    (fun _ hD => exists_unpairedPartner_of_mem_pentagonPairDecompositions R hst hX hzx hD)
    (fun D hD E hE F _ hDF hEF => ?_)
    (fun D hD F hF F' hF' hDF hDF' => ?_)
    (fun F hF => ?_)
  · rcases hDF with ⟨hsD, hrecD⟩ | ⟨_, hEqD⟩ <;> rcases hEF with ⟨hsE, hrecE⟩ | ⟨_, hEqE⟩
    · obtain ⟨hfD, hsecD⟩ := G.isEmpty_of_mem_pentagonPairDecompositions C (C.withTurnRow t) hD
      obtain ⟨hfE, hsecE⟩ := G.isEmpty_of_mem_pentagonPairDecompositions C (C.withTurnRow t) hE
      exact GridPentagonPairDecomposition.toRectangleDecomposition_injective
        (hrecD.eq_of_isRecut hrecE hfD hsecD hfE hsecE)
    · exact absurd (hEqE ▸ E.finRotate_mem_commonSideColumns rfl)
        (D.finRotate_notMem_commonSideColumns_of_sameSide_isRecut rfl hsD hrecD)
    · exact absurd (hEqD ▸ D.finRotate_mem_commonSideColumns rfl)
        (E.finRotate_notMem_commonSideColumns_of_sameSide_isRecut rfl hsE hrecE)
    · exact GridPentagonPairDecomposition.toRectangleDecomposition_injective
        (hEqD.trans hEqE.symm)
  · apply injOn_toRectangleDecomposition_crossingChangeHexagonCompositeDecompositions hX x z
      (hcomp hF) (hcomp hF')
    rcases hDF with ⟨hs, hrec⟩ | ⟨hns, hEq⟩ <;> rcases hDF' with ⟨hs', hrec'⟩ | ⟨hns', hEq'⟩
    · obtain ⟨hf, hsec⟩ := G.isEmpty_of_mem_pentagonPairDecompositions C (C.withTurnRow t) hD
      exact (D.toRectangleDecomposition.existsUnique_isRecut
        (GridRectangleDecomposition.hasOneCommonSide_of_isRecut hrec) hf hsec).unique hrec hrec'
    · exact absurd hs hns'
    · exact absurd hs' hns
    · exact hEq.symm.trans hEq'
  · obtain ⟨D, ⟨hP, hQ⟩, hr⟩ := exists_pentagonPair_of_mem_crossingChangeUnpairedHexagonComposites
      hX hzx hF
    rw [← G.commutationPentagons_def] at hP
    rw [← (G.swapColumns a b).commutationPentagons_def] at hQ
    exact ⟨D, (G.mem_pentagonPairDecompositions C (C.withTurnRow t) D).mpr ⟨hP, hQ⟩, hr⟩

/-- If the turn rows `C.turnRow` and `t` differ and the annulus squares carry no `X`-marking, then
for distinct grid states `x` and `z` the unpaired composites have the total weight of the products
of the commutation pentagon coefficients of `C` and `C.withTurnRow t` over every commutative
semiring. -/
theorem sum_crossingChangeUnpairedHexagonCompositeWeight_eq
    (R : Type*) [CommSemiring R] (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) {x z : GridState n} (hxz : x ≠ z) :
    ∑ F ∈ G.crossingChangeUnpairedHexagonComposites C t x z,
        G.crossingChangeHexagonCompositeWeight C t R F =
      ∑ y : GridState n,
        rename (Equiv.swap a b) (G.commutationPentagonCoefficient R C x y) *
          (G.swapColumns a b).commutationPentagonCoefficient R (C.withTurnRow t) y z := by
  rw [G.sum_rename_commutationPentagonCoefficient_mul_commutationPentagonCoefficient
    C (C.withTurnRow t) R,
    sum_crossingChangeUnpairedHexagonCompositeWeight_eq_sum_pentagonPairWeight
      R hst hX hxz]

end Matching

/-! ### The crossing-change homotopy equation -/

section Equation

variable (R : Type*) [CommSemiring R] [CharP R 2]

/-- **The crossing-change homotopy equation.** If the turn rows `C.turnRow` and `t` differ and the
annulus squares carry no `X`-marking, then over any commutative semiring of characteristic two the
hexagon-counting map `H = crossingChangeHomotopy` satisfies `∂ ∘ H + H ∘ ∂ = w + Ψ ∘ Φ`, where `w`
is the annulus weight. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) (c : GridChainMinus R n) :
    G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
        G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
      G.crossingChangeAnnulusWeight R C t • c +
        (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c) :=
  (unblockedDifferential_crossingChangeHomotopy_add_eq_iff_unpaired R hst hX).mpr
    (fun _ _ hxz => sum_crossingChangeUnpairedHexagonCompositeWeight_eq R hst hX hxz) c

/-- **The crossing-change homotopy equation for `O_a` on the arc of column `b`.** If the segments
of `a` and `b = finRotate n a` interleave with `O_a` on the arc of column `b`, and the crossing
change maps turn in the rows of `O_a` and `X_b`, then `∂ ∘ H + H ∘ ∂ = V_b + Ψ ∘ Φ` in
characteristic two. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq_of_mem_columnArc
    (h : G.ColumnsInterleaving a b) (hO : G.O a ∈ G.columnArc b) (hs : C.turnRow = G.O a)
    (ht : t = G.X b) (c : GridChainMinus R n) :
    G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
        G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
      (MvPolynomial.X b : MvPolynomial (Fin n) R) • c +
        (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c) := by
  have hst : C.turnRow ≠ t := by
    rw [hs, ht]
    exact ((columnsInterleaving_iff_not_columnsNoninterleaving G _ _).mp h).2.1
  exact (unblockedDifferential_crossingChangeHomotopy_add_eq_iff_unpaired_of_mem_columnArc R
    h hO hs ht).mpr
    (fun _ _ hxz => sum_crossingChangeUnpairedHexagonCompositeWeight_eq R hst
      (disjoint_crossingChangeAnnulusSquares_XSet_of_mem_columnArc h hO hs ht) hxz) c

/-- **The crossing-change homotopy equation for `O_a` off the arc of column `b`.** If the segments
of `a` and `b = finRotate n a` interleave with `O_a` off the arc of column `b`, and the crossing
change maps turn in the rows of `X_a` and `O_b`, then `∂ ∘ H + H ∘ ∂ = V_a + Ψ ∘ Φ` in
characteristic two. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq_of_notMem_columnArc
    (h : G.ColumnsInterleaving a b) (hO : G.O a ∉ G.columnArc b) (hs : C.turnRow = G.X a)
    (ht : t = G.O b) (c : GridChainMinus R n) :
    G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
        G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
      (MvPolynomial.X a : MvPolynomial (Fin n) R) • c +
        (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c) := by
  have hst : C.turnRow ≠ t := by
    rw [hs, ht]
    exact ((columnsInterleaving_iff_not_columnsNoninterleaving G _ _).mp h).2.2
  exact (unblockedDifferential_crossingChangeHomotopy_add_eq_iff_unpaired_of_notMem_columnArc R
    h hO hs ht).mpr
    (fun _ _ hxz => sum_crossingChangeUnpairedHexagonCompositeWeight_eq R hst
      (disjoint_crossingChangeAnnulusSquares_XSet_of_notMem_columnArc h hO hs ht) hxz) c

/-- On a cycle `z` of `GC⁻(G)`, the round trip `Ψ ∘ Φ` equals multiplication by the annulus weight
up to the boundary of `H z`. -/
theorem commutationMap_withTurnRow_commutationMap_of_mem_ker (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) {z : GridChainMinus R n}
    (hz : z ∈ LinearMap.ker (G.unblockedDifferential R)) :
    (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C z) =
      G.crossingChangeAnnulusWeight R C t • z +
        G.unblockedDifferential R (G.crossingChangeHomotopy R C t z) := by
  have h := unblockedDifferential_crossingChangeHomotopy_add_eq R hst hX z
  rw [LinearMap.mem_ker.mp hz, map_zero, add_zero] at h
  rw [h, ← add_assoc,
    add_self_eq_zero_of_charTwo (MvPolynomial (Fin n) R) (G.crossingChangeAnnulusWeight R C t • z),
    zero_add]

/-- On a cycle `z` of `GC⁻(G)`, when `a` and `b` interleave with `O_a` on the arc of column `b` and
the crossing-change maps turn at `O_a` and `X_b`, `Ψ(Φ z) = V_b • z + ∂(H z)`. -/
theorem commutationMap_withTurnRow_commutationMap_of_mem_ker_of_mem_columnArc
    (h : G.ColumnsInterleaving a b) (hO : G.O a ∈ G.columnArc b) (hs : C.turnRow = G.O a)
    (ht : t = G.X b) {z : GridChainMinus R n}
    (hz : z ∈ LinearMap.ker (G.unblockedDifferential R)) :
    (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C z) =
      (MvPolynomial.X b : MvPolynomial (Fin n) R) • z +
        G.unblockedDifferential R (G.crossingChangeHomotopy R C t z) := by
  rw [← crossingChangeAnnulusWeight_eq_X_next_of_mem_columnArc R h hO hs ht]
  exact commutationMap_withTurnRow_commutationMap_of_mem_ker R
    (by rw [hs, ht]; exact ((columnsInterleaving_iff_not_columnsNoninterleaving G _ _).mp h).2.1)
    (disjoint_crossingChangeAnnulusSquares_XSet_of_mem_columnArc h hO hs ht) hz

/-- On a cycle `z` of `GC⁻(G)`, when `a` and `b` interleave with `O_a` off the arc of column `b`
and the crossing-change maps turn at `X_a` and `O_b`, `Ψ(Φ z) = V_a • z + ∂(H z)`. -/
theorem commutationMap_withTurnRow_commutationMap_of_mem_ker_of_notMem_columnArc
    (h : G.ColumnsInterleaving a b) (hO : G.O a ∉ G.columnArc b) (hs : C.turnRow = G.X a)
    (ht : t = G.O b) {z : GridChainMinus R n}
    (hz : z ∈ LinearMap.ker (G.unblockedDifferential R)) :
    (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C z) =
      (MvPolynomial.X a : MvPolynomial (Fin n) R) • z +
        G.unblockedDifferential R (G.crossingChangeHomotopy R C t z) := by
  rw [← crossingChangeAnnulusWeight_eq_X_column_of_notMem_columnArc R h hO hs ht]
  exact commutationMap_withTurnRow_commutationMap_of_mem_ker R
    (by rw [hs, ht]; exact ((columnsInterleaving_iff_not_columnsNoninterleaving G _ _).mp h).2.2)
    (disjoint_crossingChangeAnnulusSquares_XSet_of_notMem_columnArc h hO hs ht) hz

end Equation

end TauCeti.GridDiagram
