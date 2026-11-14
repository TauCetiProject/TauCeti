/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Unpaired
public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.SameSide
public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.TerminalInitialSum
import TauCeti.Algebra.BigOperators.Finset.Pairing
import TauCeti.Algebra.CharP.Two

/-!
# The homotopy equation of a grid crossing change

Let `C` be a column turn at the columns `a = C.column` and `b = finRotate n a` of a grid diagram
`G`, turning in row `s = C.turnRow`, and let `t` be a second row distinct from `s` such that the
annulus squares `GridDiagram.crossingChangeAnnulusSquares C t` carry no `X`-marking. Write
`Φ : GC⁻(G) → GC⁻(G')` for the commutation map of `C`, where `G' = G.swapColumns a b`,
`Ψ : GC⁻(G') → GC⁻(G)` for the commutation map of `G'` turning in row `t`, and
`H : GC⁻(G) → GC⁻(G)` for `GridDiagram.crossingChangeHomotopy` with corners in the rows `s` and
`t`. This file proves the crossing-change homotopy equation

  `∂ ∘ H + H ∘ ∂ = w • 1 + Ψ ∘ Φ`

over every commutative semiring `R` of characteristic two, where
`w = G.crossingChangeAnnulusWeight R C t`. Specializing to interleaving columns gives the two
homotopy equations of Ozsváth--Stipsicz--Szabó, Section 6.1, with `w = V_b` when `O_a` lies on the
arc of column `b` and `w = V_a` when `O_a` lies off it.

After the diagonal, disjoint-side, and same-side recut cancellations
(`GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_iff_unpaired`), it remains to
identify, off the diagonal, the sum of weights of
`GridDiagram.crossingChangeUnpairedHexagonComposites` with the round-trip pentagon-pair coefficient
sum. Expanding each commutation pentagon coefficient into its terminal-side and initial-side parts
terminal--terminal, initial--initial, terminal--initial (already summed in
`Homotopy/TerminalInitialSum.lean`), and initial--terminal. Over any commutative semiring, each
branch matches bijectively with its partner finset inside the unpaired composites, the four partner
finsets are pairwise disjoint, and by
`GridDiagram.exists_pentagonPair_of_mem_crossingChangeUnpairedHexagonComposites` their union
exhausts all off-diagonal unpaired composites.

## Main definitions

* `TauCeti.GridDiagram.crossingChangeTerminalPairs`,
  `TauCeti.GridDiagram.crossingChangeTerminalPartners`: counted terminal--terminal pentagon pairs
  and their recut image among unpaired composites.
* `TauCeti.GridDiagram.crossingChangeInitialPairs`,
  `TauCeti.GridDiagram.crossingChangeInitialPartners`: counted initial--initial pentagon pairs
  and their recut image among unpaired composites.
* `TauCeti.GridDiagram.crossingChangeInitialTerminalPairs`,
  `TauCeti.GridDiagram.crossingChangeInitialTerminalPartners`: counted initial--terminal pentagon
  pairs and their image among unpaired composites.

## Main results

* `TauCeti.GridDiagram.sum_crossingChangeUnpairedHexagonComposites_eq`: off the diagonal, the
  unpaired hexagon composites have the same total weight as the round-trip pentagon-coefficient
  products, over every commutative semiring.
* `TauCeti.GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq`: the crossing-change
  homotopy equation `∂ ∘ H + H ∘ ∂ = w • c + Ψ(Φ(c))` in characteristic two.
* `TauCeti.GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_of_mem_columnArc` and
  `TauCeti.GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_of_notMem_columnArc`:
  the specialized homotopy equations with `w = V_b` and `w = V_a` for interleaving columns.
* `TauCeti.GridDiagram.commutationMap_withTurnRow_commutationMap_of_mem_ker`: on cycles, the round
  trip `Ψ ∘ Φ` equals multiplication by the annulus weight up to a boundary.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Section 6.1.
* M. Kendall, *Crossing change maps in filtered grid homology*, arXiv:2303.04227, Section 3.
-/

public section

namespace TauCeti.GridDiagram

open MvPolynomial

variable {n : ℕ} (G : GridDiagram n) (C : ColumnTurn n) (t : Fin n)

local notation "a" => C.column
local notation "b" => finRotate n C.column

/-! ### Initial--terminal pentagon pairs and partners -/

/-- The initial--terminal pentagon pairs in the round trip through the exchanged diagram.
The first pentagon turns on its initial side in row `C.turnRow`, the second on its terminal side
in row `t`. -/
noncomputable def crossingChangeInitialTerminalPairs (x z : GridState n) :
    Finset (GridTwoStepDecomposition (GridInitialPentagonBetween a C.turnRow)
      (GridPentagonBetween a t) x z) :=
  GridTwoStepDecomposition.decompositionsOf (G.initialPentagons C)
    ((G.swapColumns a b).pentagons (C.withTurnRow t)) x z

/-- An initial--terminal pair is counted exactly when each of its pentagons is counted. -/
@[simp]
theorem mem_crossingChangeInitialTerminalPairs {x z : GridState n}
    (D : GridTwoStepDecomposition (GridInitialPentagonBetween a C.turnRow)
      (GridPentagonBetween a t) x z) :
    D ∈ G.crossingChangeInitialTerminalPairs C t x z ↔
      D.first ∈ G.initialPentagons C x D.middle ∧
        D.second ∈ (G.swapColumns a b).pentagons (C.withTurnRow t) D.middle z := by
  rw [crossingChangeInitialTerminalPairs, GridTwoStepDecomposition.mem_decompositionsOf]

/-- The exact image of counted initial--terminal pairs among the unpaired crossing-change
composites. -/
noncomputable def crossingChangeInitialTerminalPartners (x z : GridState n) :
    Finset (GridHexagonCompositeDecomposition a C.turnRow t x z) := by
  classical
  exact (G.crossingChangeUnpairedHexagonComposites C t x z).filter fun F =>
    ∃ D ∈ G.crossingChangeInitialTerminalPairs C t x z,
      (⟨D.middle, D.first.toGridRectangleBetween, D.second.toGridRectangleBetween⟩ :
        GridRectangleDecomposition x z) = F.toRectangleDecomposition

/-- Initial--terminal partners are the unpaired composites sharing the two rectangles of a counted
initial--terminal pair. -/
@[simp]
theorem mem_crossingChangeInitialTerminalPartners {x z : GridState n}
    (F : GridHexagonCompositeDecomposition a C.turnRow t x z) :
    F ∈ G.crossingChangeInitialTerminalPartners C t x z ↔
      F ∈ G.crossingChangeUnpairedHexagonComposites C t x z ∧
        ∃ D ∈ G.crossingChangeInitialTerminalPairs C t x z,
          (⟨D.middle, D.first.toGridRectangleBetween, D.second.toGridRectangleBetween⟩ :
            GridRectangleDecomposition x z) = F.toRectangleDecomposition := by
  classical
  simp only [crossingChangeInitialTerminalPartners, Finset.mem_filter]

/-- Every initial--terminal partner belongs to the unpaired-composite sum. -/
theorem crossingChangeInitialTerminalPartners_subset (x z : GridState n) :
    G.crossingChangeInitialTerminalPartners C t x z ⊆
      G.crossingChangeUnpairedHexagonComposites C t x z :=
  fun F hF => ((G.mem_crossingChangeInitialTerminalPartners C t F).mp hF).1

/-- Off the diagonal, for distinct turn rows and an annulus carrying no `X`-marking, the
initial--terminal terms of the round-trip coefficient sum have the same total weight as their
unpaired hexagon-composite partners over every commutative semiring. -/
theorem sum_rename_initialPentagonCoefficient_mul_eq_sum_crossingChangeInitialTerminalPartners
    (R : Type*) [CommSemiring R] (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hzx : z ≠ x) :
    (∑ y : GridState n,
      rename (Equiv.swap a b) (G.initialPentagonCoefficient R C x y) *
        (G.swapColumns a b).pentagonCoefficient R (C.withTurnRow t) y z) =
      ∑ F ∈ G.crossingChangeInitialTerminalPartners C t x z,
        G.crossingChangeHexagonCompositeWeight C t R F := by
  classical
  let rect (D : GridTwoStepDecomposition (GridInitialPentagonBetween a C.turnRow)
      (GridPentagonBetween a t) x z) : GridRectangleDecomposition x z :=
    ⟨D.middle, D.first.toGridRectangleBetween, D.second.toGridRectangleBetween⟩
  have hinj : Function.Injective rect := fun _ _ h =>
    GridTwoStepDecomposition.ext_of_middle_eq
      (congrArg (fun F : GridRectangleDecomposition x z => F.middle) h)
  have hcounted {F} (hF : F ∈ G.crossingChangeInitialTerminalPartners C t x z) :=
    ((G.mem_crossingChangeUnpairedHexagonComposites C t F).mp
      (G.crossingChangeInitialTerminalPartners_subset C t x z hF)).1
  simp_rw [G.initialPentagonCoefficient_def R C,
    (G.swapColumns a b).pentagonCoefficient_def R (C.withTurnRow t),
    map_sum, Finset.sum_mul_sum]
  rw [← GridTwoStepDecomposition.sum_decompositionsOf]
  refine Finset.sum_bij_of_rel (fun D F => rect D = F.toRectangleDecomposition)
    (fun D hD => ?_) (fun _ _ _ _ _ _ hDF hEF => hinj (hDF.trans hEF.symm))
    (fun _ _ F hF F' hF' hDF hDF' => ?_)
    (fun F hF => ((G.mem_crossingChangeInitialTerminalPartners C t F).mp hF).2)
  · obtain ⟨hP, hQ⟩ := (G.mem_crossingChangeInitialTerminalPairs C t D).mp hD
    obtain ⟨F, ⟨hF, hFD, hw⟩, -⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_initialTerminalPentagonPair
        R hst hX D.first D.second hP hQ hzx
    exact ⟨F, (G.mem_crossingChangeInitialTerminalPartners C t F).mpr
      ⟨hF, D, hD, hFD.symm⟩, hFD.symm, hw.symm⟩
  · exact injOn_toRectangleDecomposition_crossingChangeHexagonCompositeDecompositions hX x z
      (hcounted hF) (hcounted hF') (hDF.symm.trans hDF')

/-! ### Same-side pentagon pairs and partners -/

/-- The terminal--terminal pentagon pairs in the round trip through the exchanged diagram. -/
noncomputable def crossingChangeTerminalPairs (x z : GridState n) :
    Finset (GridTwoStepDecomposition (GridPentagonBetween a C.turnRow)
      (GridPentagonBetween a t) x z) :=
  GridTwoStepDecomposition.decompositionsOf (G.pentagons C)
    ((G.swapColumns a b).pentagons (C.withTurnRow t)) x z

/-- A terminal--terminal pair is counted exactly when each of its pentagons is counted. -/
@[simp]
theorem mem_crossingChangeTerminalPairs {x z : GridState n}
    (D : GridTwoStepDecomposition (GridPentagonBetween a C.turnRow)
      (GridPentagonBetween a t) x z) :
    D ∈ G.crossingChangeTerminalPairs C t x z ↔
      D.first ∈ G.pentagons C x D.middle ∧
        D.second ∈ (G.swapColumns a b).pentagons (C.withTurnRow t) D.middle z := by
  rw [crossingChangeTerminalPairs, GridTwoStepDecomposition.mem_decompositionsOf]

/-- The unpaired crossing-change composites obtained by recutting counted terminal--terminal
pentagon pairs. -/
noncomputable def crossingChangeTerminalPartners (x z : GridState n) :
    Finset (GridHexagonCompositeDecomposition a C.turnRow t x z) := by
  classical
  exact (G.crossingChangeUnpairedHexagonComposites C t x z).filter fun F =>
    ∃ D ∈ G.crossingChangeTerminalPairs C t x z,
      GridRectangleDecomposition.IsRecut
        ⟨D.middle, D.first.toGridRectangleBetween, D.second.toGridRectangleBetween⟩
        F.toRectangleDecomposition

/-- Terminal partners are the unpaired composites recutting a counted terminal--terminal pair. -/
@[simp]
theorem mem_crossingChangeTerminalPartners {x z : GridState n}
    (F : GridHexagonCompositeDecomposition a C.turnRow t x z) :
    F ∈ G.crossingChangeTerminalPartners C t x z ↔
      F ∈ G.crossingChangeUnpairedHexagonComposites C t x z ∧
        ∃ D ∈ G.crossingChangeTerminalPairs C t x z,
          GridRectangleDecomposition.IsRecut
            ⟨D.middle, D.first.toGridRectangleBetween, D.second.toGridRectangleBetween⟩
            F.toRectangleDecomposition := by
  classical
  simp only [crossingChangeTerminalPartners, Finset.mem_filter]

/-- Every terminal partner belongs to the unpaired-composite sum. -/
theorem crossingChangeTerminalPartners_subset (x z : GridState n) :
    G.crossingChangeTerminalPartners C t x z ⊆
      G.crossingChangeUnpairedHexagonComposites C t x z :=
  fun F hF => ((G.mem_crossingChangeTerminalPartners C t F).mp hF).1

/-- Off the diagonal, when the annulus carries no `X`-marking, the terminal--terminal terms of the
round-trip coefficient sum equal the sum of weights of their recut partners over every commutative
semiring. -/
theorem sum_rename_pentagonCoefficient_mul_eq_sum_crossingChangeTerminalPartners
    (R : Type*) [CommSemiring R] (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hzx : z ≠ x) :
    (∑ y : GridState n,
      rename (Equiv.swap a b) (G.pentagonCoefficient R C x y) *
        (G.swapColumns a b).pentagonCoefficient R (C.withTurnRow t) y z) =
      ∑ F ∈ G.crossingChangeTerminalPartners C t x z,
        G.crossingChangeHexagonCompositeWeight C t R F := by
  classical
  let rect (D : GridTwoStepDecomposition (GridPentagonBetween a C.turnRow)
      (GridPentagonBetween a t) x z) : GridRectangleDecomposition x z :=
    ⟨D.middle, D.first.toGridRectangleBetween, D.second.toGridRectangleBetween⟩
  have hcounted {F} (hF : F ∈ G.crossingChangeTerminalPartners C t x z) :=
    ((G.mem_crossingChangeUnpairedHexagonComposites C t F).mp
      (G.crossingChangeTerminalPartners_subset C t x z hF)).1
  have hempty {D} (hD : D ∈ G.crossingChangeTerminalPairs C t x z) :
      (rect D).first.IsEmpty ∧ (rect D).second.IsEmpty :=
    ⟨((G.mem_pentagons D.first).mp ((G.mem_crossingChangeTerminalPairs C t D).mp hD).1).1,
      (((G.swapColumns a b).mem_pentagons (C := C.withTurnRow t) D.second).mp
        ((G.mem_crossingChangeTerminalPairs C t D).mp hD).2).1⟩
  simp_rw [G.pentagonCoefficient_def R C,
    (G.swapColumns a b).pentagonCoefficient_def R (C.withTurnRow t),
    map_sum, Finset.sum_mul_sum]
  rw [← GridTwoStepDecomposition.sum_decompositionsOf]
  refine Finset.sum_bij_of_rel (fun D F => (rect D).IsRecut F.toRectangleDecomposition)
    (fun D hD => ?_) (fun D hD E hE _ _ hDF hEF => ?_)
    (fun D hD F hF F' hF' hDF hDF' => ?_)
    (fun F hF => ((G.mem_crossingChangeTerminalPartners C t F).mp hF).2)
  · obtain ⟨hP, hQ⟩ := (G.mem_crossingChangeTerminalPairs C t D).mp hD
    obtain ⟨⟨F, ⟨hF, hrecut⟩, -⟩, hw⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_terminalPentagonPair
        R hX D.first D.second hP hQ hzx
    exact ⟨F, (G.mem_crossingChangeTerminalPartners C t F).mpr ⟨hF, D, hD, hrecut⟩, hrecut,
      (hw F hF hrecut).symm⟩
  · have hDE := hDF.eq_of_isRecut hEF (hempty hD).1 (hempty hD).2 (hempty hE).1 (hempty hE).2
    exact GridTwoStepDecomposition.ext_of_middle_eq
      (congrArg (fun R : GridRectangleDecomposition x z => R.middle) hDE)
  · exact injOn_toRectangleDecomposition_crossingChangeHexagonCompositeDecompositions hX x z
      (hcounted hF) (hcounted hF')
      (((rect D).existsUnique_isRecut (GridRectangleDecomposition.hasOneCommonSide_of_isRecut hDF)
        (hempty hD).1 (hempty hD).2).unique hDF hDF')

/-- The initial--initial pentagon pairs in the round trip through the exchanged diagram. -/
noncomputable def crossingChangeInitialPairs (x z : GridState n) :
    Finset (GridTwoStepDecomposition (GridInitialPentagonBetween a C.turnRow)
      (GridInitialPentagonBetween a t) x z) :=
  GridTwoStepDecomposition.decompositionsOf (G.initialPentagons C)
    ((G.swapColumns a b).initialPentagons (C.withTurnRow t)) x z

/-- An initial--initial pair is counted exactly when each of its pentagons is counted. -/
@[simp]
theorem mem_crossingChangeInitialPairs {x z : GridState n}
    (D : GridTwoStepDecomposition (GridInitialPentagonBetween a C.turnRow)
      (GridInitialPentagonBetween a t) x z) :
    D ∈ G.crossingChangeInitialPairs C t x z ↔
      D.first ∈ G.initialPentagons C x D.middle ∧
        D.second ∈ (G.swapColumns a b).initialPentagons (C.withTurnRow t) D.middle z := by
  rw [crossingChangeInitialPairs, GridTwoStepDecomposition.mem_decompositionsOf]

/-- The unpaired crossing-change composites obtained by recutting counted initial--initial pentagon
pairs. -/
noncomputable def crossingChangeInitialPartners (x z : GridState n) :
    Finset (GridHexagonCompositeDecomposition a C.turnRow t x z) := by
  classical
  exact (G.crossingChangeUnpairedHexagonComposites C t x z).filter fun F =>
    ∃ D ∈ G.crossingChangeInitialPairs C t x z,
      GridRectangleDecomposition.IsRecut
        ⟨D.middle, D.first.toGridRectangleBetween, D.second.toGridRectangleBetween⟩
        F.toRectangleDecomposition

/-- Initial partners are the unpaired composites recutting a counted initial--initial pair. -/
@[simp]
theorem mem_crossingChangeInitialPartners {x z : GridState n}
    (F : GridHexagonCompositeDecomposition a C.turnRow t x z) :
    F ∈ G.crossingChangeInitialPartners C t x z ↔
      F ∈ G.crossingChangeUnpairedHexagonComposites C t x z ∧
        ∃ D ∈ G.crossingChangeInitialPairs C t x z,
          GridRectangleDecomposition.IsRecut
            ⟨D.middle, D.first.toGridRectangleBetween, D.second.toGridRectangleBetween⟩
            F.toRectangleDecomposition := by
  classical
  simp only [crossingChangeInitialPartners, Finset.mem_filter]

/-- Every initial partner belongs to the unpaired-composite sum. -/
theorem crossingChangeInitialPartners_subset (x z : GridState n) :
    G.crossingChangeInitialPartners C t x z ⊆
      G.crossingChangeUnpairedHexagonComposites C t x z :=
  fun F hF => ((G.mem_crossingChangeInitialPartners C t F).mp hF).1

/-- Off the diagonal, when the annulus carries no `X`-marking, the initial--initial terms of the
round-trip coefficient sum equal the sum of weights of their recut partners over every commutative
semiring. -/
theorem sum_rename_initialPentagonCoefficient_mul_eq_sum_crossingChangeInitialPartners
    (R : Type*) [CommSemiring R] (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hzx : z ≠ x) :
    (∑ y : GridState n,
      rename (Equiv.swap a b) (G.initialPentagonCoefficient R C x y) *
        (G.swapColumns a b).initialPentagonCoefficient R (C.withTurnRow t) y z) =
      ∑ F ∈ G.crossingChangeInitialPartners C t x z,
        G.crossingChangeHexagonCompositeWeight C t R F := by
  classical
  let rect (D : GridTwoStepDecomposition (GridInitialPentagonBetween a C.turnRow)
      (GridInitialPentagonBetween a t) x z) : GridRectangleDecomposition x z :=
    ⟨D.middle, D.first.toGridRectangleBetween, D.second.toGridRectangleBetween⟩
  have hcounted {F} (hF : F ∈ G.crossingChangeInitialPartners C t x z) :=
    ((G.mem_crossingChangeUnpairedHexagonComposites C t F).mp
      (G.crossingChangeInitialPartners_subset C t x z hF)).1
  have hempty {D} (hD : D ∈ G.crossingChangeInitialPairs C t x z) :
      (rect D).first.IsEmpty ∧ (rect D).second.IsEmpty :=
    ⟨((G.mem_initialPentagons D.first).mp ((G.mem_crossingChangeInitialPairs C t D).mp hD).1).1,
      (((G.swapColumns a b).mem_initialPentagons (C := C.withTurnRow t) D.second).mp
        ((G.mem_crossingChangeInitialPairs C t D).mp hD).2).1⟩
  simp_rw [G.initialPentagonCoefficient_def R C,
    (G.swapColumns a b).initialPentagonCoefficient_def R (C.withTurnRow t),
    map_sum, Finset.sum_mul_sum]
  rw [← GridTwoStepDecomposition.sum_decompositionsOf]
  refine Finset.sum_bij_of_rel (fun D F => (rect D).IsRecut F.toRectangleDecomposition)
    (fun D hD => ?_) (fun D hD E hE _ _ hDF hEF => ?_)
    (fun D hD F hF F' hF' hDF hDF' => ?_)
    (fun F hF => ((G.mem_crossingChangeInitialPartners C t F).mp hF).2)
  · obtain ⟨hP, hQ⟩ := (G.mem_crossingChangeInitialPairs C t D).mp hD
    obtain ⟨⟨F, ⟨hF, hrecut⟩, -⟩, hw⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_initialPentagonPair
        R hX D.first D.second hP hQ hzx
    exact ⟨F, (G.mem_crossingChangeInitialPartners C t F).mpr ⟨hF, D, hD, hrecut⟩, hrecut,
      (hw F hF hrecut).symm⟩
  · have hDE := hDF.eq_of_isRecut hEF (hempty hD).1 (hempty hD).2 (hempty hE).1 (hempty hE).2
    exact GridTwoStepDecomposition.ext_of_middle_eq
      (congrArg (fun R : GridRectangleDecomposition x z => R.middle) hDE)
  · exact injOn_toRectangleDecomposition_crossingChangeHexagonCompositeDecompositions hX x z
      (hcounted hF) (hcounted hF')
      (((rect D).existsUnique_isRecut (GridRectangleDecomposition.hasOneCommonSide_of_isRecut hDF)
        (hempty hD).1 (hempty hD).2).unique hDF hDF')

/-! ### Disjointness and exhaustion of the four partner families -/

/-- No unpaired composite recuts both a terminal--terminal and an initial--initial pentagon pair:
recut uniqueness would equate their first rectangles, whose initial sides differ. -/
theorem disjoint_crossingChangeTerminalPartners_crossingChangeInitialPartners
    {x z : GridState n} :
    Disjoint (G.crossingChangeTerminalPartners C t x z)
      (G.crossingChangeInitialPartners C t x z) := by
  rw [Finset.disjoint_left]
  intro F hT hI
  obtain ⟨-, D, hD, hDF⟩ := (G.mem_crossingChangeTerminalPartners C t F).mp hT
  obtain ⟨-, E, hE, hEF⟩ := (G.mem_crossingChangeInitialPartners C t F).mp hI
  obtain ⟨hP, hQ⟩ := (G.mem_crossingChangeTerminalPairs C t D).mp hD
  obtain ⟨hP', hQ'⟩ := (G.mem_crossingChangeInitialPairs C t E).mp hE
  have hDE := hDF.eq_of_isRecut hEF
    ((G.mem_pentagons D.first).mp hP).1
    (((G.swapColumns a b).mem_pentagons (C := C.withTurnRow t) D.second).mp hQ).1
    ((G.mem_initialPentagons E.first).mp hP').1
    (((G.swapColumns a b).mem_initialPentagons (C := C.withTurnRow t) E.second).mp hQ').1
  have hleft := congrArg (fun R : GridRectangleDecomposition x z => R.first.left) hDE
  exact D.first.left_ne (hleft.trans E.first.left_eq)

/-- No unpaired composite shares its rectangles with both a terminal--initial and an
initial--terminal pentagon pair: their first rectangles have distinct initial sides. -/
theorem disjoint_crossingChangeTerminalInitialPartners_crossingChangeInitialTerminalPartners
    {x z : GridState n} :
    Disjoint (G.crossingChangeTerminalInitialPartners C t x z)
      (G.crossingChangeInitialTerminalPartners C t x z) := by
  rw [Finset.disjoint_left]
  intro F hTI hIT
  obtain ⟨-, D, -, hDF⟩ := (G.mem_crossingChangeTerminalInitialPartners C t F).mp hTI
  obtain ⟨-, E, -, hEF⟩ := (G.mem_crossingChangeInitialTerminalPartners C t F).mp hIT
  have hleft := congrArg (fun R : GridRectangleDecomposition x z => R.first.left)
    (hDF.trans hEF.symm)
  exact D.first.left_ne (hleft.trans E.first.left_eq)

open scoped Classical in
/-- The replaced grid line `b` is never a common side of a same-side recut partner, whereas it is a
common side of every mixed-side partner; hence the two partner unions are disjoint. -/
theorem disjoint_crossingChangeSameSidePartners_crossingChangeMixedSidePartners
    {x z : GridState n} :
    Disjoint
      (G.crossingChangeTerminalPartners C t x z ∪ G.crossingChangeInitialPartners C t x z)
      (G.crossingChangeTerminalInitialPartners C t x z ∪
        G.crossingChangeInitialTerminalPartners C t x z) := by
  rw [Finset.disjoint_left]
  intro F hS hM
  have hb : b ∈ F.toRectangleDecomposition.commonSideColumns := by
    rcases Finset.mem_union.mp hM with hTI | hIT
    · obtain ⟨-, D, -, hDF⟩ := (G.mem_crossingChangeTerminalInitialPartners C t F).mp hTI
      simp [← hDF, D.first.right_eq, D.second.left_eq]
    · obtain ⟨-, D, -, hDF⟩ := (G.mem_crossingChangeInitialTerminalPartners C t F).mp hIT
      simp [← hDF, D.first.left_eq, D.second.right_eq]
  rcases Finset.mem_union.mp hS with hT | hI
  · obtain ⟨-, D, -, hrecut⟩ := (G.mem_crossingChangeTerminalPartners C t F).mp hT
    have hcommon := hrecut.isRecutOfRightEqRight (D.first.right_eq.trans D.second.right_eq.symm)
    exact hcommon.first_right_notMem_commonSideColumns
      (by simpa only [D.first.right_eq] using hb)
  · obtain ⟨-, D, -, hrecut⟩ := (G.mem_crossingChangeInitialPartners C t F).mp hI
    have hcommon := hrecut.isRecutOfLeftEqLeft (D.first.left_eq.trans D.second.left_eq.symm)
    exact hcommon.first_left_notMem_commonSideColumns
      (by simpa only [D.first.left_eq] using hb)

open scoped Classical in
/-- Off the diagonal, when the annulus carries no `X`-marking, the unpaired crossing-change
composites partition into the four pentagon-partner families. -/
theorem crossingChangeUnpairedHexagonComposites_eq_union
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) {x z : GridState n} (hzx : z ≠ x) :
    G.crossingChangeUnpairedHexagonComposites C t x z =
      (G.crossingChangeTerminalPartners C t x z ∪ G.crossingChangeInitialPartners C t x z) ∪
        (G.crossingChangeTerminalInitialPartners C t x z ∪
          G.crossingChangeInitialTerminalPartners C t x z) := by
  refine Finset.Subset.antisymm (fun F hF => ?_) (Finset.union_subset
    (Finset.union_subset (G.crossingChangeTerminalPartners_subset C t x z)
      (G.crossingChangeInitialPartners_subset C t x z))
    (Finset.union_subset (G.crossingChangeTerminalInitialPartners_subset C t x z)
      (G.crossingChangeInitialTerminalPartners_subset C t x z)))
  obtain ⟨⟨m, P | P, Q | Q⟩, ⟨hP, hQ⟩, hD⟩ :=
    exists_pentagonPair_of_mem_crossingChangeUnpairedHexagonComposites hX hzx hF
  · rcases hD with ⟨-, hrec⟩ | ⟨hside, -⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        ((G.mem_crossingChangeTerminalPartners C t F).mpr ⟨hF, ⟨m, P, Q⟩,
          (G.mem_crossingChangeTerminalPairs C t _).mpr
            ⟨Finset.inl_mem_disjSum.mp hP, Finset.inl_mem_disjSum.mp hQ⟩,
          by simpa [GridPentagonPairDecomposition.toRectangleDecomposition] using hrec⟩))
    · simp at hside
  · rcases hD with ⟨hside, -⟩ | ⟨-, hrect⟩
    · simp at hside
    · exact Finset.mem_union_right _ (Finset.mem_union_left _
        ((G.mem_crossingChangeTerminalInitialPartners C t F).mpr ⟨hF, ⟨m, P, Q⟩,
          (G.mem_crossingChangeTerminalInitialPairs C t _).mpr
            ⟨Finset.inl_mem_disjSum.mp hP, Finset.inr_mem_disjSum.mp hQ⟩,
          by simpa [GridPentagonPairDecomposition.toRectangleDecomposition] using hrect⟩))
  · rcases hD with ⟨hside, -⟩ | ⟨-, hrect⟩
    · simp at hside
    · exact Finset.mem_union_right _ (Finset.mem_union_right _
        ((G.mem_crossingChangeInitialTerminalPartners C t F).mpr ⟨hF, ⟨m, P, Q⟩,
          (G.mem_crossingChangeInitialTerminalPairs C t _).mpr
            ⟨Finset.inr_mem_disjSum.mp hP, Finset.inl_mem_disjSum.mp hQ⟩,
          by simpa [GridPentagonPairDecomposition.toRectangleDecomposition] using hrect⟩))
  · rcases hD with ⟨-, hrec⟩ | ⟨hside, -⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        ((G.mem_crossingChangeInitialPartners C t F).mpr ⟨hF, ⟨m, P, Q⟩,
          (G.mem_crossingChangeInitialPairs C t _).mpr
            ⟨Finset.inr_mem_disjSum.mp hP, Finset.inr_mem_disjSum.mp hQ⟩,
          by simpa [GridPentagonPairDecomposition.toRectangleDecomposition] using hrec⟩))
    · simp at hside

/-! ### The off-diagonal weight identity and homotopy equations -/

/-- **Off-diagonal crossing-change coefficient identity.** For distinct turn rows and an annulus
carrying no `X`-marking, between distinct grid states `x ≠ z` the unpaired hexagon composites have
the same total polynomial weight as the round-trip pentagon-coefficient products, over every
commutative semiring. -/
theorem sum_crossingChangeUnpairedHexagonComposites_eq
    (R : Type*) [CommSemiring R] (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hxz : x ≠ z) :
    ∑ D ∈ G.crossingChangeUnpairedHexagonComposites C t x z,
        G.crossingChangeHexagonCompositeWeight C t R D =
      ∑ y : GridState n,
        rename (Equiv.swap a b) (G.commutationPentagonCoefficient R C x y) *
          (G.swapColumns a b).commutationPentagonCoefficient R (C.withTurnRow t) y z := by
  classical
  rw [G.crossingChangeUnpairedHexagonComposites_eq_union C t hX hxz.symm,
    Finset.sum_union
      (G.disjoint_crossingChangeSameSidePartners_crossingChangeMixedSidePartners C t),
    Finset.sum_union (G.disjoint_crossingChangeTerminalPartners_crossingChangeInitialPartners C t),
    Finset.sum_union
      (G.disjoint_crossingChangeTerminalInitialPartners_crossingChangeInitialTerminalPartners C t),
    ← G.sum_rename_pentagonCoefficient_mul_eq_sum_crossingChangeTerminalPartners
      C t R hX hxz.symm,
    ← G.sum_rename_initialPentagonCoefficient_mul_eq_sum_crossingChangeInitialPartners
      C t R hX hxz.symm,
    ← G.sum_rename_pentagonCoefficient_mul_eq_sum_crossingChangeTerminalInitialPartners
      C t R hst hX hxz.symm,
    ← G.sum_rename_initialPentagonCoefficient_mul_eq_sum_crossingChangeInitialTerminalPartners
      C t R hst hX hxz.symm]
  simp_rw [← Finset.sum_add_distrib, G.commutationPentagonCoefficient_def R C,
    (G.swapColumns a b).commutationPentagonCoefficient_def R (C.withTurnRow t), map_add]
  refine Finset.sum_congr rfl fun _ _ => ?_
  ring

/-- **The crossing-change homotopy equation.** If the turn rows `C.turnRow` and `t` differ and the
annulus squares carry no `X`-marking, then over any commutative semiring of characteristic two the
hexagon-counting map `H` satisfies `∂ ∘ H + H ∘ ∂ = w • 1 + Ψ ∘ Φ`, where `w` is the annulus
weight. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq
    (R : Type*) [CommSemiring R] [CharP R 2] (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) (c : GridChainMinus R n) :
    G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
        G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
      G.crossingChangeAnnulusWeight R C t • c +
        (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c) :=
  (unblockedDifferential_crossingChangeHomotopy_add_eq_iff_unpaired R hst hX).mpr
    (fun _ _ hxz => G.sum_crossingChangeUnpairedHexagonComposites_eq C t R hst hX hxz) c

/-- **The crossing-change homotopy equation**, for markings in the cyclic order
`O_b, O_a, X_b, X_a`: when the columns `a` and `b = finRotate n a` interleave with `O_a` on the arc
of column `b`, and the crossing-change maps turn in the rows of `O_a` and `X_b`,
`∂ ∘ H + H ∘ ∂ = V_b • 1 + Ψ ∘ Φ` over any commutative semiring of characteristic two. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq_of_mem_columnArc
    (R : Type*) [CommSemiring R] [CharP R 2]
    (h : G.ColumnsInterleaving a b) (hO : G.O a ∈ G.columnArc b) (hs : C.turnRow = G.O a)
    (ht : t = G.X b) (c : GridChainMinus R n) :
    G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
        G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
      (MvPolynomial.X b : MvPolynomial (Fin n) R) • c +
        (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c) :=
  (unblockedDifferential_crossingChangeHomotopy_add_eq_iff_unpaired_of_mem_columnArc
    R h hO hs ht).mpr
    (fun _ _ hxz => G.sum_crossingChangeUnpairedHexagonComposites_eq C t R
      (by rw [hs, ht]; exact ((columnsInterleaving_iff_not_columnsNoninterleaving G _ _).mp h).2.1)
      (disjoint_crossingChangeAnnulusSquares_XSet_of_mem_columnArc h hO hs ht) hxz) c

/-- **The crossing-change homotopy equation**, for markings in the cyclic order
`O_b, X_a, X_b, O_a`: when the columns `a` and `b = finRotate n a` interleave with `O_a` off the arc
of column `b`, and the crossing-change maps turn in the rows of `X_a` and `O_b`,
`∂ ∘ H + H ∘ ∂ = V_a • 1 + Ψ ∘ Φ` over any commutative semiring of characteristic two. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq_of_notMem_columnArc
    (R : Type*) [CommSemiring R] [CharP R 2]
    (h : G.ColumnsInterleaving a b) (hO : G.O a ∉ G.columnArc b) (hs : C.turnRow = G.X a)
    (ht : t = G.O b) (c : GridChainMinus R n) :
    G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
        G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
      (MvPolynomial.X a : MvPolynomial (Fin n) R) • c +
        (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c) :=
  (unblockedDifferential_crossingChangeHomotopy_add_eq_iff_unpaired_of_notMem_columnArc
    R h hO hs ht).mpr
    (fun _ _ hxz => G.sum_crossingChangeUnpairedHexagonComposites_eq C t R
      (by rw [hs, ht]; exact ((columnsInterleaving_iff_not_columnsNoninterleaving G _ _).mp h).2.2)
      (disjoint_crossingChangeAnnulusSquares_XSet_of_notMem_columnArc h hO hs ht) hxz) c

/-- On a cycle `z` of `GC⁻(G)`, the round trip `Ψ ∘ Φ` through the exchanged diagram equals scalar
multiplication by the annulus weight up to the boundary of `H z`. -/
theorem commutationMap_withTurnRow_commutationMap_of_mem_ker
    (R : Type*) [CommSemiring R] [CharP R 2] (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) {z : GridChainMinus R n}
    (hz : z ∈ LinearMap.ker (G.unblockedDifferential R)) :
    (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C z) =
      G.crossingChangeAnnulusWeight R C t • z +
        G.unblockedDifferential R (G.crossingChangeHomotopy R C t z) := by
  have h := G.unblockedDifferential_crossingChangeHomotopy_add_eq C t R hst hX z
  rw [LinearMap.mem_ker.mp hz, map_zero, add_zero] at h
  rw [h, ← add_assoc, add_self_eq_zero_of_charTwo (MvPolynomial (Fin n) R) _, zero_add]

end TauCeti.GridDiagram
