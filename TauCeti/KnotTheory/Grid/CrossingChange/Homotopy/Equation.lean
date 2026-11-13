/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Unpaired
public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.SameSide
public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Mixed
import TauCeti.Algebra.BigOperators.Finset.Pairing

/-!
# The homotopy equation of a crossing change

Let `C` be a column turn at the columns `a` and `b = finRotate n a` of a grid diagram `G`, turning
in row `s`, and let `t ≠ s` be a second row such that the annulus squares
`GridDiagram.crossingChangeAnnulusSquares C t` carry no `X`-marking. Write
`Φ : GC⁻(G) → GC⁻(G')` for the commutation map of `C`, where `G' = G.swapColumns a b`,
`Ψ : GC⁻(G') → GC⁻(G)` for the commutation map of `G'` turning in row `t`, and `H` for the
hexagon-counting map `GridDiagram.crossingChangeHomotopy`. This file proves the homotopy equation

  `∂ ∘ H + H ∘ ∂ = w • 1 + Ψ ∘ Φ`

over every commutative semiring of characteristic two, where `w` is the annulus weight. For the
two crossing changes between interleaving columns, `w` is the variable `V_b` or `V_a`. These are
the two homotopies of the crossing change inequality for `τ`.

The diagonal, disjoint and recut cancellations reduce the equation to the statement that, off the
diagonal, the unpaired hexagon composites have the total weight of the pentagon pairs counted by
`Ψ ∘ Φ` (`GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_iff_unpaired`). Here
these two families are matched bijectively, with equal weights. A pair whose two pentagons turn
on the same side of the replaced grid line `b` is matched with the composite recutting its
rectangles, and a pair turning on opposite sides with the composite having its rectangles. Each
pair has exactly one partner (`Homotopy.SameSide`, `Homotopy.Mixed`), and every unpaired
composite is a partner (`Homotopy.Unpaired`). Two pairs never share a partner: same-side pairs
are recovered from their recut, mixed-side pairs from their rectangles, and `b` is a common side
of the rectangles of every pair but not of the recut of a same-side pair.

## Main definitions and results

* `TauCeti.GridDiagram.pentagonPairDecompositions` and `TauCeti.GridDiagram.pentagonPairWeight`
  from `Commutation.Homotopy.Decomposition` supply the pairs counted by `Ψ ∘ Φ` and their weights.
* `TauCeti.GridDiagram.sum_pentagonPairWeight_eq_sum_crossingChangeUnpairedHexagonComposites`:
  off the diagonal, the pentagon pairs and the unpaired composites have the same total weight.
* `TauCeti.GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq`: the homotopy
  equation `∂ ∘ H + H ∘ ∂ = w • 1 + Ψ ∘ Φ` in characteristic two.
* `TauCeti.GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_of_mem_columnArc` and
  `TauCeti.GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_of_notMem_columnArc`:
  the composites of the crossing change maps are homotopic to multiplication by `V_b` and by
  `V_a`.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Section 6.1, Lemma 6.1.4: the homotopies of the composites of the
  crossing change maps.
* M. Kendall, *Crossing change maps in filtered grid homology*, arXiv:2303.04227, Section 3: the
  homotopy equations for the hexagons with corners at the two turn points.
-/

public section

namespace TauCeti.GridDiagram

open MvPolynomial

variable {n : ℕ} (G : GridDiagram n) (C : ColumnTurn n) (t : Fin n)

local notation "a" => C.column
local notation "b" => finRotate n C.column

variable (R : Type*) [CommSemiring R]

/-! ### Matching pentagon pairs with unpaired composites -/

variable {G C t}

/-- Off the diagonal, every counted pentagon pair has a partner among the unpaired composites of
the same weight: the recut of its rectangles if its pentagons turn on the same side, a composite
with its rectangles otherwise. -/
private theorem exists_unpaired_partner (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) {x z : GridState n} (hzx : z ≠ x)
    {D : GridPentagonPairDecomposition a C.turnRow a t x z}
    (hD : D ∈ G.pentagonPairDecompositions C (C.withTurnRow t) x z) :
    ∃ F ∈ G.crossingChangeUnpairedHexagonComposites C t x z,
      (D.first.isLeft = D.second.isLeft ∧
          D.toRectangleDecomposition.IsRecut F.toRectangleDecomposition ∨
        D.first.isLeft ≠ D.second.isLeft ∧
          D.toRectangleDecomposition = F.toRectangleDecomposition) ∧
        G.pentagonPairWeight C (C.withTurnRow t) R D =
          G.crossingChangeHexagonCompositeWeight C t R F := by
  obtain ⟨hP, hQ⟩ := (G.mem_pentagonPairDecompositions C (C.withTurnRow t) D).mp hD
  simp only [pentagonPairWeight_def]
  rcases D with ⟨m, P | P, Q | Q⟩ <;>
    simp only [G.inl_mem_commutationPentagons C, G.inr_mem_commutationPentagons C,
      (G.swapColumns a b).inl_mem_commutationPentagons (C.withTurnRow t),
      (G.swapColumns a b).inr_mem_commutationPentagons (C.withTurnRow t),
      G.commutationPentagonWeight_inl C R, G.commutationPentagonWeight_inr C R,
      (G.swapColumns a b).commutationPentagonWeight_inl (C.withTurnRow t) R,
      (G.swapColumns a b).commutationPentagonWeight_inr (C.withTurnRow t) R] at hP hQ ⊢
  · obtain ⟨⟨F, ⟨hF, hrecut⟩, -⟩, hw⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_terminalPentagonPair R hX P Q hP hQ
        hzx
    refine ⟨F, hF, Or.inl ⟨rfl, ?_⟩, (hw F hF hrecut).symm⟩
    simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inl] using hrecut
  · obtain ⟨F, ⟨hF, hFD, hw⟩, -⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_terminalInitialPentagonPair R hst hX
        P Q hP hQ hzx
    refine ⟨F, hF, Or.inr ⟨by simp, ?_⟩, hw.symm⟩
    simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inl,
      GridCommutationPentagonBetween.toGridRectangleBetween_inr] using hFD.symm
  · obtain ⟨F, ⟨hF, hFD, hw⟩, -⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_initialTerminalPentagonPair R hst hX
        P Q hP hQ hzx
    refine ⟨F, hF, Or.inr ⟨by simp, ?_⟩, hw.symm⟩
    simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inl,
      GridCommutationPentagonBetween.toGridRectangleBetween_inr] using hFD.symm
  · obtain ⟨⟨F, ⟨hF, hrecut⟩, -⟩, hw⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_initialPentagonPair R hX P Q hP hQ
        hzx
    refine ⟨F, hF, Or.inl ⟨rfl, ?_⟩, (hw F hF hrecut).symm⟩
    simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inr] using hrecut

/-- **Pentagon pairs and unpaired composites.** If the turn rows `s` and `t` differ and the annulus
squares carry no `X`-marking, then off the diagonal the pentagon pairs counted by the round trip
`Ψ ∘ Φ` and the unpaired composites of the crossing change homotopy equation have the same total
weight, over every commutative semiring. -/
theorem sum_pentagonPairWeight_eq_sum_crossingChangeUnpairedHexagonComposites
    (hst : C.turnRow ≠ t) (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hzx : z ≠ x) :
    ∑ D ∈ G.pentagonPairDecompositions C (C.withTurnRow t) x z,
        G.pentagonPairWeight C (C.withTurnRow t) R D =
      ∑ F ∈ G.crossingChangeUnpairedHexagonComposites C t x z,
        G.crossingChangeHexagonCompositeWeight C t R F := by
  have hcounted {F} (hF : F ∈ G.crossingChangeUnpairedHexagonComposites C t x z) :=
    ((G.mem_crossingChangeUnpairedHexagonComposites C t F).mp hF).1
  refine Finset.sum_bij_of_rel
    (fun D F => D.first.isLeft = D.second.isLeft ∧
        D.toRectangleDecomposition.IsRecut F.toRectangleDecomposition ∨
      D.first.isLeft ≠ D.second.isLeft ∧
        D.toRectangleDecomposition = F.toRectangleDecomposition)
    (fun D hD => exists_unpaired_partner R hst hX hzx hD) (fun D hD E hE F _ hDF hEF => ?_)
    (fun D hD F hF F' hF' hDF hDF' => ?_) (fun F hF => ?_)
  · -- A pair is recovered from its partner.
    obtain ⟨hfD, hsD⟩ := G.isEmpty_of_mem_pentagonPairDecompositions C (C.withTurnRow t) hD
    obtain ⟨hfE, hsE⟩ := G.isEmpty_of_mem_pentagonPairDecompositions C (C.withTurnRow t) hE
    apply GridPentagonPairDecomposition.toRectangleDecomposition_injective
    rcases hDF with ⟨hsideD, hrecD⟩ | ⟨-, hrectD⟩ <;> rcases hEF with ⟨hsideE, hrecE⟩ | ⟨-, hrectE⟩
    · exact hrecD.eq_of_isRecut hrecE hfD hsD hfE hsE
    · exact (GridPentagonPairDecomposition.finRotate_notMem_commonSideColumns_of_isRecut rfl
        hsideD hrecD (hrectE ▸ E.finRotate_mem_commonSideColumns rfl)).elim
    · exact (GridPentagonPairDecomposition.finRotate_notMem_commonSideColumns_of_isRecut rfl
        hsideE hrecE (hrectD ▸ D.finRotate_mem_commonSideColumns rfl)).elim
    · exact hrectD.trans hrectE.symm
  · -- A pair has only one partner.
    apply injOn_toRectangleDecomposition_crossingChangeHexagonCompositeDecompositions hX x z
      (hcounted hF) (hcounted hF')
    rcases hDF with ⟨hside, hrec⟩ | ⟨hside, hrect⟩ <;>
      rcases hDF' with ⟨hside', hrec'⟩ | ⟨hside', hrect'⟩
    · obtain ⟨hf, hs⟩ := G.isEmpty_of_mem_pentagonPairDecompositions C (C.withTurnRow t) hD
      exact (D.toRectangleDecomposition.existsUnique_isRecut
        (GridRectangleDecomposition.hasOneCommonSide_of_isRecut hrec) hf hs).unique hrec hrec'
    · exact (hside' hside).elim
    · exact (hside hside').elim
    · exact hrect.symm.trans hrect'
  · -- Every unpaired composite is a partner.
    exact exists_pentagonPair_of_mem_crossingChangeUnpairedHexagonComposites hX hzx hF

/-! ### The homotopy equation -/

variable [CharP R 2]

/-- **The homotopy equation of a crossing change.** If the turn rows `s` and `t` differ and the
annulus squares carry no `X`-marking, then over a commutative semiring of characteristic two the
hexagon-counting map `H` satisfies `∂ ∘ H + H ∘ ∂ = w • 1 + Ψ ∘ Φ`, where `w` is the annulus weight
and `Ψ ∘ Φ` is the round trip of the commutation maps of `G` turning in row `s` and of
`G.swapColumns a b` turning in row `t`. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) (c : GridChainMinus R n) :
    G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
        G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
      G.crossingChangeAnnulusWeight R C t • c +
        (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c) := by
  refine (unblockedDifferential_crossingChangeHomotopy_add_eq_iff_unpaired R hst hX).mpr
    (fun x z hxz => ?_) c
  rw [G.sum_rename_commutationPentagonCoefficient_mul_commutationPentagonCoefficient
    C (C.withTurnRow t) R,
    sum_pentagonPairWeight_eq_sum_crossingChangeUnpairedHexagonComposites R hst hX (Ne.symm hxz)]

/-- **The homotopy of the composite of the crossing change maps**, for markings in the order
`O_b, O_a, X_b, X_a`. If the segments of the columns `a` and `b = finRotate n a` interleave with
`O_a` on the arc of column `b`, the crossing change maps turn in the rows of `O_a` and `X_b`, and
`R` has characteristic two, then `∂ ∘ H + H ∘ ∂ = V_b + Ψ ∘ Φ`. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq_of_mem_columnArc
    (h : G.ColumnsInterleaving a b) (hO : G.O a ∈ G.columnArc b) (hs : C.turnRow = G.O a)
    (ht : t = G.X b) (c : GridChainMinus R n) :
    G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
        G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
      (MvPolynomial.X b : MvPolynomial (Fin n) R) • c +
        (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c) := by
  rw [← crossingChangeAnnulusWeight_eq_X_next_of_mem_columnArc R h hO hs ht]
  exact unblockedDifferential_crossingChangeHomotopy_add_eq R
    (by rw [hs, ht]; exact ((columnsInterleaving_iff_not_columnsNoninterleaving G _ _).mp h).2.1)
    (disjoint_crossingChangeAnnulusSquares_XSet_of_mem_columnArc h hO hs ht) c

/-- **The homotopy of the composite of the crossing change maps**, for markings in the order
`O_b, X_a, X_b, O_a`. If the segments of the columns `a` and `b = finRotate n a` interleave with
`O_a` off the arc of column `b`, the crossing change maps turn in the rows of `X_a` and `O_b`, and
`R` has characteristic two, then `∂ ∘ H + H ∘ ∂ = V_a + Ψ ∘ Φ`. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq_of_notMem_columnArc
    (h : G.ColumnsInterleaving a b) (hO : G.O a ∉ G.columnArc b) (hs : C.turnRow = G.X a)
    (ht : t = G.O b) (c : GridChainMinus R n) :
    G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
        G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
      (MvPolynomial.X a : MvPolynomial (Fin n) R) • c +
        (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c) := by
  rw [← crossingChangeAnnulusWeight_eq_X_column_of_notMem_columnArc R h hO hs ht]
  exact unblockedDifferential_crossingChangeHomotopy_add_eq R
    (by rw [hs, ht]; exact ((columnsInterleaving_iff_not_columnsNoninterleaving G _ _).mp h).2.2)
    (disjoint_crossingChangeAnnulusSquares_XSet_of_notMem_columnArc h hO hs ht) c

end TauCeti.GridDiagram
