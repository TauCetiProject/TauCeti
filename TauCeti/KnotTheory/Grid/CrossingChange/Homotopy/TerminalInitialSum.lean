/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Mixed
import TauCeti.Algebra.BigOperators.Finset.Pairing

/-!
# Summing terminal--initial crossing-change partners

The round trip of two crossing-change maps counts pairs of pentagons. This file matches
its terminal--initial pairs with their exact image among the unpaired hexagon composites
of the crossing-change homotopy. Off the diagonal the matching is one-to-one and preserves
polynomial weight, including the variable renaming from the semilinear forward map.
This identifies one entire branch of the round-trip coefficient sum with its matching
contribution to the homotopy equation. Only the terminal--initial branch is treated here.

The geometric input is
`GridDiagram.existsUnique_crossingChangeUnpairedHexagonComposite_of_terminalInitialPentagonPair`.

## Main definitions and results

* `GridDiagram.crossingChangeTerminalInitialPairs`: the counted terminal--initial pairs.
* `GridDiagram.crossingChangeTerminalInitialPartners`: their exact image among unpaired composites.
* The terminal--initial branch sum equals its partner sum off the diagonal, for distinct turn
  rows and an annulus without `X` markings.

The finite-sum organization follows the commutation homotopy's
`GridDiagram.sum_pentagonPairWeight_mixedSide_eq_sum_partners`.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 6.1;
Kendall, *Crossing change maps in filtered grid homology*, arXiv:2303.04227, Section 3.
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnTurn n) (t : Fin n)

local notation "a" => C.column
local notation "b" => finRotate n C.column

/-- The terminal--initial pentagon pairs in the round trip through the exchanged diagram.
The first pentagon turns in row `C.turnRow`, the second in row `t`. -/
noncomputable def crossingChangeTerminalInitialPairs (x z : GridState n) :
    Finset (GridTwoStepDecomposition (GridPentagonBetween a C.turnRow)
      (GridInitialPentagonBetween a t) x z) :=
  GridTwoStepDecomposition.decompositionsOf (G.pentagons C)
    ((G.swapColumns a b).initialPentagons (C.withTurnRow t)) x z

/-- A terminal--initial pair is counted exactly when each of its pentagons is counted. -/
@[simp]
theorem mem_crossingChangeTerminalInitialPairs {x z : GridState n}
    (D : GridTwoStepDecomposition (GridPentagonBetween a C.turnRow)
      (GridInitialPentagonBetween a t) x z) :
    D ∈ G.crossingChangeTerminalInitialPairs C t x z ↔
      D.first ∈ G.pentagons C x D.middle ∧
        D.second ∈ (G.swapColumns a b).initialPentagons (C.withTurnRow t) D.middle z := by
  rw [crossingChangeTerminalInitialPairs, GridTwoStepDecomposition.mem_decompositionsOf]

/-- The exact image of terminal--initial pairs among the unpaired crossing-change composites.
Membership retains the underlying two rectangles, rather than only the total domain. -/
noncomputable def crossingChangeTerminalInitialPartners (x z : GridState n) :
    Finset (GridHexagonCompositeDecomposition a C.turnRow t x z) := by
  classical
  exact (G.crossingChangeUnpairedHexagonComposites C t x z).filter fun F =>
    ∃ D ∈ G.crossingChangeTerminalInitialPairs C t x z,
      (⟨D.middle, D.first.toGridRectangleBetween, D.second.toGridRectangleBetween⟩ :
        GridRectangleDecomposition x z) = F.toRectangleDecomposition

/-- Partners are exactly the unpaired composites sharing the two rectangles of a counted pair. -/
@[simp]
theorem mem_crossingChangeTerminalInitialPartners {x z : GridState n}
    (F : GridHexagonCompositeDecomposition a C.turnRow t x z) :
    F ∈ G.crossingChangeTerminalInitialPartners C t x z ↔
      F ∈ G.crossingChangeUnpairedHexagonComposites C t x z ∧
        ∃ D ∈ G.crossingChangeTerminalInitialPairs C t x z,
          (⟨D.middle, D.first.toGridRectangleBetween, D.second.toGridRectangleBetween⟩ :
            GridRectangleDecomposition x z) = F.toRectangleDecomposition := by
  classical
  simp only [crossingChangeTerminalInitialPartners, Finset.mem_filter]

/-- Every terminal--initial partner is a term of the unpaired-composite sum. -/
theorem crossingChangeTerminalInitialPartners_subset (x z : GridState n) :
    G.crossingChangeTerminalInitialPartners C t x z ⊆
      G.crossingChangeUnpairedHexagonComposites C t x z :=
  fun F hF => ((G.mem_crossingChangeTerminalInitialPartners C t F).mp hF).1

/-- Off the diagonal (`z ≠ x`), for distinct turn rows and with no `X` marking in the
crossing-change annulus, the terminal--initial terms of the round-trip coefficient sum have the
same total weight as their unpaired hexagon-composite partners. No characteristic-two assumption
is needed for this matching; it holds over every commutative semiring. -/
theorem sum_rename_pentagonCoefficient_mul_eq_sum_crossingChangeTerminalInitialPartners
    (R : Type*) [CommSemiring R] (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hzx : z ≠ x) :
    (∑ y : GridState n,
      MvPolynomial.rename (Equiv.swap a b) (G.pentagonCoefficient R C x y) *
        (G.swapColumns a b).initialPentagonCoefficient R (C.withTurnRow t) y z) =
      ∑ F ∈ G.crossingChangeTerminalInitialPartners C t x z,
        G.crossingChangeHexagonCompositeWeight C t R F := by
  classical
  let rect (D : GridTwoStepDecomposition (GridPentagonBetween a C.turnRow)
      (GridInitialPentagonBetween a t) x z) : GridRectangleDecomposition x z :=
    ⟨D.middle, D.first.toGridRectangleBetween, D.second.toGridRectangleBetween⟩
  have hinj : Function.Injective rect := by
    intro D E h
    exact GridTwoStepDecomposition.ext_of_middle_eq
      (congrArg (fun F : GridRectangleDecomposition x z => F.middle) h)
  have hcounted {F} (hF : F ∈ G.crossingChangeTerminalInitialPartners C t x z) :=
    ((G.mem_crossingChangeUnpairedHexagonComposites C t F).mp
      (G.crossingChangeTerminalInitialPartners_subset C t x z hF)).1
  simp_rw [G.pentagonCoefficient_def R C,
    (G.swapColumns a b).initialPentagonCoefficient_def R (C.withTurnRow t),
    map_sum, Finset.sum_mul_sum]
  rw [← GridTwoStepDecomposition.sum_decompositionsOf]
  refine Finset.sum_bij_of_rel (fun D F => rect D = F.toRectangleDecomposition)
    (fun D hD => ?_) (fun D _ E _ F _ hDF hEF => hinj (hDF.trans hEF.symm))
    (fun D _ F hF F' hF' hDF hDF' => ?_)
    (fun F hF => ((G.mem_crossingChangeTerminalInitialPartners C t F).mp hF).2)
  · obtain ⟨hP, hQ⟩ := (G.mem_crossingChangeTerminalInitialPairs C t D).mp hD
    obtain ⟨F, ⟨hF, hFD, hw⟩, -⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_terminalInitialPentagonPair
        R hst hX D.first D.second hP hQ hzx
    exact ⟨F, (G.mem_crossingChangeTerminalInitialPartners C t F).mpr
      ⟨hF, D, hD, hFD.symm⟩, hFD.symm, hw.symm⟩
  · exact injOn_toRectangleDecomposition_crossingChangeHexagonCompositeDecompositions hX x z
      (hcounted hF) (hcounted hF') (hDF.symm.trans hDF')

end TauCeti.GridDiagram
