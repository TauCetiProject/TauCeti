/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.SameSide
public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.TerminalInitialSum
public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Unpaired
import TauCeti.Algebra.BigOperators.Finset.Pairing
import TauCeti.Algebra.CharP.Two

/-!
# The homotopy equation of a grid crossing change

Let `C` be a column turn at the adjacent columns `a = C.column` and `b = finRotate n a` of a grid
diagram `G`, let `t` be a second turn row distinct from `C.turnRow`, and write
`G' = G.swapColumns a b`. Write `Φ : GC⁻(G) → GC⁻(G')` for the commutation map of `C`,
`Ψ : GC⁻(G') → GC⁻(G)` for the commutation map of `G'` turning at the same columns in row `t`,
`H : GC⁻(G) → GC⁻(G)` for the hexagon-counting map `GridDiagram.crossingChangeHomotopy`, and `w`
for the annulus weight `GridDiagram.crossingChangeAnnulusWeight`. When the crossing-change annulus
squares carry no `X`-marking, this file proves the chain homotopy equation

  `∂ ∘ H + H ∘ ∂ = w • id + Ψ ∘ Φ`

over every commutative semiring of characteristic two.

By the diagonal, disjoint, and recut cancellations
(`GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_iff_unpaired`), the equation
reduces to matching, between distinct grid states `x` and `z`, the unpaired hexagon composites with
the four branches of pentagon pairs counted by `Ψ ∘ Φ`. The terminal--initial branch is matched in
`CrossingChange/Homotopy/TerminalInitialSum.lean`. Here we establish the analogous weight-preserving
bijections for the initial--terminal, terminal--terminal, and initial--initial branches over an
arbitrary commutative semiring, show that the four partner finsets partition the unpaired hexagon
composites off the diagonal, and deduce the chain homotopy equations for both cyclic orders of
interleaving column markings (`w = V_b` and `w = V_a`).

## Main definitions and results

* `TauCeti.GridDiagram.crossingChangeInitialTerminalPartners`,
  `TauCeti.GridDiagram.crossingChangeTerminalPartners`,
  `TauCeti.GridDiagram.crossingChangeInitialPartners`: the exact images of the remaining three
  pentagon-pair branches inside `GridDiagram.crossingChangeUnpairedHexagonComposites`.
* `TauCeti.GridDiagram.sum_crossingChangeUnpairedHexagonComposites_eq_sum_pentagonCoefficient`:
  off the diagonal, the total weight of the unpaired hexagon composites equals the round-trip
  pentagon-coefficient sum over any commutative semiring.
* `TauCeti.GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq`: the general
  crossing-change homotopy equation `∂ ∘ H + H ∘ ∂ = w • c + Ψ(Φ(c))` in characteristic two.
* `TauCeti.GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_of_mem_columnArc` and
  `TauCeti.GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_of_notMem_columnArc`:
  the specialized homotopy equations with `w = V_b` and `w = V_a` for adjacent interleaving
  columns.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Section 6.1, Lemma 6.1.4.
* M. Kendall, *Crossing change maps in filtered grid homology*, arXiv:2303.04227, Section 3.
-/

public section

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnTurn n) (t : Fin n)

local notation "a" => C.column
local notation "b" => finRotate n C.column

/-! ### Initial--terminal partners -/

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

/-- The exact image of initial--terminal pairs among the unpaired crossing-change composites. -/
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

/-- Every initial--terminal partner is an unpaired crossing-change composite. -/
theorem crossingChangeInitialTerminalPartners_subset (x z : GridState n) :
    G.crossingChangeInitialTerminalPartners C t x z ⊆
      G.crossingChangeUnpairedHexagonComposites C t x z :=
  fun F hF => ((G.mem_crossingChangeInitialTerminalPartners C t F).mp hF).1

/-- Off the diagonal (`z ≠ x`), for distinct turn rows and with no `X`-marking in the
crossing-change annulus, the initial--terminal terms of the round-trip coefficient sum have the
same total weight as their unpaired hexagon-composite partners over every commutative semiring. -/
theorem sum_rename_initialPentagonCoefficient_mul_eq_sum_crossingChangeInitialTerminalPartners
    (R : Type*) [CommSemiring R] (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hzx : z ≠ x) :
    (∑ y : GridState n,
      MvPolynomial.rename (Equiv.swap a b) (G.initialPentagonCoefficient R C x y) *
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
    (fun D hD => ?_) (fun D _ E _ F _ hDF hEF => hinj (hDF.trans hEF.symm))
    (fun D _ F hF F' hF' hDF hDF' => ?_)
    (fun F hF => ((G.mem_crossingChangeInitialTerminalPartners C t F).mp hF).2)
  · obtain ⟨hP, hQ⟩ := (G.mem_crossingChangeInitialTerminalPairs C t D).mp hD
    obtain ⟨F, ⟨hF, hFD, hw⟩, -⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_initialTerminalPentagonPair
        R hst hX D.first D.second hP hQ hzx
    exact ⟨F, (G.mem_crossingChangeInitialTerminalPartners C t F).mpr
      ⟨hF, D, hD, hFD.symm⟩, hFD.symm, hw.symm⟩
  · exact injOn_toRectangleDecomposition_crossingChangeHexagonCompositeDecompositions hX x z
      (hcounted hF) (hcounted hF') (hDF.symm.trans hDF')

/-! ### Terminal--terminal partners -/

/-- The terminal--terminal pentagon pairs in the round trip through the exchanged diagram.
Both pentagons turn on their terminal side, first in row `C.turnRow` and then in row `t`. -/
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

/-- The exact recut image of terminal--terminal pairs among the unpaired crossing-change
composites. -/
noncomputable def crossingChangeTerminalPartners (x z : GridState n) :
    Finset (GridHexagonCompositeDecomposition a C.turnRow t x z) := by
  classical
  exact (G.crossingChangeUnpairedHexagonComposites C t x z).filter fun F =>
    ∃ D ∈ G.crossingChangeTerminalPairs C t x z,
      GridRectangleDecomposition.IsRecut
        (⟨D.middle, D.first.toGridRectangleBetween, D.second.toGridRectangleBetween⟩ :
          GridRectangleDecomposition x z) F.toRectangleDecomposition

/-- Terminal--terminal partners are the unpaired composites recutting the two rectangles of a
counted terminal--terminal pair. -/
@[simp]
theorem mem_crossingChangeTerminalPartners {x z : GridState n}
    (F : GridHexagonCompositeDecomposition a C.turnRow t x z) :
    F ∈ G.crossingChangeTerminalPartners C t x z ↔
      F ∈ G.crossingChangeUnpairedHexagonComposites C t x z ∧
        ∃ D ∈ G.crossingChangeTerminalPairs C t x z,
          GridRectangleDecomposition.IsRecut
            (⟨D.middle, D.first.toGridRectangleBetween, D.second.toGridRectangleBetween⟩ :
              GridRectangleDecomposition x z) F.toRectangleDecomposition := by
  classical
  simp only [crossingChangeTerminalPartners, Finset.mem_filter]

/-- Every terminal--terminal partner is an unpaired crossing-change composite. -/
theorem crossingChangeTerminalPartners_subset (x z : GridState n) :
    G.crossingChangeTerminalPartners C t x z ⊆
      G.crossingChangeUnpairedHexagonComposites C t x z :=
  fun F hF => ((G.mem_crossingChangeTerminalPartners C t F).mp hF).1

/-- Off the diagonal (`z ≠ x`), with no `X`-marking in the crossing-change annulus, the
terminal--terminal terms of the round-trip coefficient sum have the same total weight as their
recut partners among the unpaired hexagon composites over every commutative semiring. -/
theorem sum_rename_pentagonCoefficient_mul_eq_sum_crossingChangeTerminalPartners
    (R : Type*) [CommSemiring R]
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hzx : z ≠ x) :
    (∑ y : GridState n,
      MvPolynomial.rename (Equiv.swap a b) (G.pentagonCoefficient R C x y) *
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
      (rect D).first.IsEmpty ∧ (rect D).second.IsEmpty := by
    obtain ⟨hP, hQ⟩ := (G.mem_crossingChangeTerminalPairs C t D).mp hD
    exact ⟨((G.mem_pentagons D.first).mp hP).1,
      (((G.swapColumns a b).mem_pentagons (C := C.withTurnRow t) D.second).mp hQ).1⟩
  simp_rw [G.pentagonCoefficient_def R C,
    (G.swapColumns a b).pentagonCoefficient_def R (C.withTurnRow t),
    map_sum, Finset.sum_mul_sum]
  rw [← GridTwoStepDecomposition.sum_decompositionsOf]
  refine Finset.sum_bij_of_rel (fun D F => (rect D).IsRecut F.toRectangleDecomposition)
    (fun D hD => ?_) (fun D hD E hE F _ hDF hEF => ?_)
    (fun D hD F hF F' hF' hDF hDF' => ?_)
    (fun F hF => ((G.mem_crossingChangeTerminalPartners C t F).mp hF).2)
  · obtain ⟨hP, hQ⟩ := (G.mem_crossingChangeTerminalPairs C t D).mp hD
    obtain ⟨⟨F, ⟨hF, hrec⟩, -⟩, hw⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_terminalPentagonPair
        R hX D.first D.second hP hQ hzx
    exact ⟨F, (G.mem_crossingChangeTerminalPartners C t F).mpr ⟨hF, D, hD, hrec⟩,
      hrec, (hw F hF hrec).symm⟩
  · have hrect := hDF.eq_of_isRecut hEF (hempty hD).1 (hempty hD).2 (hempty hE).1 (hempty hE).2
    exact GridTwoStepDecomposition.ext_of_middle_eq
      (congrArg (fun F : GridRectangleDecomposition x z => F.middle) hrect)
  · have hone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hDF
    have hFF' := ((rect D).existsUnique_isRecut hone (hempty hD).1 (hempty hD).2).unique hDF hDF'
    exact injOn_toRectangleDecomposition_crossingChangeHexagonCompositeDecompositions hX x z
      (hcounted hF) (hcounted hF') hFF'

/-! ### Initial--initial partners -/

/-- The initial--initial pentagon pairs in the round trip through the exchanged diagram.
Both pentagons turn on their initial side, first in row `C.turnRow` and then in row `t`. -/
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

/-- The exact recut image of initial--initial pairs among the unpaired crossing-change
composites. -/
noncomputable def crossingChangeInitialPartners (x z : GridState n) :
    Finset (GridHexagonCompositeDecomposition a C.turnRow t x z) := by
  classical
  exact (G.crossingChangeUnpairedHexagonComposites C t x z).filter fun F =>
    ∃ D ∈ G.crossingChangeInitialPairs C t x z,
      GridRectangleDecomposition.IsRecut
        (⟨D.middle, D.first.toGridRectangleBetween, D.second.toGridRectangleBetween⟩ :
          GridRectangleDecomposition x z) F.toRectangleDecomposition

/-- Initial--initial partners are the unpaired composites recutting the two rectangles of a counted
initial--initial pair. -/
@[simp]
theorem mem_crossingChangeInitialPartners {x z : GridState n}
    (F : GridHexagonCompositeDecomposition a C.turnRow t x z) :
    F ∈ G.crossingChangeInitialPartners C t x z ↔
      F ∈ G.crossingChangeUnpairedHexagonComposites C t x z ∧
        ∃ D ∈ G.crossingChangeInitialPairs C t x z,
          GridRectangleDecomposition.IsRecut
            (⟨D.middle, D.first.toGridRectangleBetween, D.second.toGridRectangleBetween⟩ :
              GridRectangleDecomposition x z) F.toRectangleDecomposition := by
  classical
  simp only [crossingChangeInitialPartners, Finset.mem_filter]

/-- Every initial--initial partner is an unpaired crossing-change composite. -/
theorem crossingChangeInitialPartners_subset (x z : GridState n) :
    G.crossingChangeInitialPartners C t x z ⊆
      G.crossingChangeUnpairedHexagonComposites C t x z :=
  fun F hF => ((G.mem_crossingChangeInitialPartners C t F).mp hF).1

/-- Off the diagonal (`z ≠ x`), with no `X`-marking in the crossing-change annulus, the
initial--initial terms of the round-trip coefficient sum have the same total weight as their recut
partners among the unpaired hexagon composites over every commutative semiring. -/
theorem sum_rename_initialPentagonCoefficient_mul_eq_sum_crossingChangeInitialPartners
    (R : Type*) [CommSemiring R]
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hzx : z ≠ x) :
    (∑ y : GridState n,
      MvPolynomial.rename (Equiv.swap a b) (G.initialPentagonCoefficient R C x y) *
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
      (rect D).first.IsEmpty ∧ (rect D).second.IsEmpty := by
    obtain ⟨hP, hQ⟩ := (G.mem_crossingChangeInitialPairs C t D).mp hD
    exact ⟨((G.mem_initialPentagons D.first).mp hP).1,
      (((G.swapColumns a b).mem_initialPentagons (C := C.withTurnRow t) D.second).mp hQ).1⟩
  simp_rw [G.initialPentagonCoefficient_def R C,
    (G.swapColumns a b).initialPentagonCoefficient_def R (C.withTurnRow t),
    map_sum, Finset.sum_mul_sum]
  rw [← GridTwoStepDecomposition.sum_decompositionsOf]
  refine Finset.sum_bij_of_rel (fun D F => (rect D).IsRecut F.toRectangleDecomposition)
    (fun D hD => ?_) (fun D hD E hE F _ hDF hEF => ?_)
    (fun D hD F hF F' hF' hDF hDF' => ?_)
    (fun F hF => ((G.mem_crossingChangeInitialPartners C t F).mp hF).2)
  · obtain ⟨hP, hQ⟩ := (G.mem_crossingChangeInitialPairs C t D).mp hD
    obtain ⟨⟨F, ⟨hF, hrec⟩, -⟩, hw⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_initialPentagonPair
        R hX D.first D.second hP hQ hzx
    exact ⟨F, (G.mem_crossingChangeInitialPartners C t F).mpr ⟨hF, D, hD, hrec⟩,
      hrec, (hw F hF hrec).symm⟩
  · have hrect := hDF.eq_of_isRecut hEF (hempty hD).1 (hempty hD).2 (hempty hE).1 (hempty hE).2
    exact GridTwoStepDecomposition.ext_of_middle_eq
      (congrArg (fun F : GridRectangleDecomposition x z => F.middle) hrect)
  · have hone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hDF
    have hFF' := ((rect D).existsUnique_isRecut hone (hempty hD).1 (hempty hD).2).unique hDF hDF'
    exact injOn_toRectangleDecomposition_crossingChangeHexagonCompositeDecompositions hX x z
      (hcounted hF) (hcounted hF') hFF'

/-! ### Partitioning the unpaired composites -/

/-- A terminal--terminal recut partner does not have `b = finRotate n C.column` as a common side
column of its two rectangles. -/
private theorem finRotate_notMem_commonSideColumns_of_mem_crossingChangeTerminalPartners
    {x z : GridState n} {F : GridHexagonCompositeDecomposition a C.turnRow t x z}
    (hF : F ∈ G.crossingChangeTerminalPartners C t x z) :
    b ∉ F.toRectangleDecomposition.commonSideColumns := by
  obtain ⟨-, D, -, hrecut⟩ := (G.mem_crossingChangeTerminalPartners C t F).mp hF
  have hcommon := hrecut.isRecutOfRightEqRight (D.first.right_eq.trans D.second.right_eq.symm)
  simpa only [D.first.right_eq] using hcommon.first_right_notMem_commonSideColumns

/-- An initial--initial recut partner does not have `b = finRotate n C.column` as a common side
column of its two rectangles. -/
private theorem finRotate_notMem_commonSideColumns_of_mem_crossingChangeInitialPartners
    {x z : GridState n} {F : GridHexagonCompositeDecomposition a C.turnRow t x z}
    (hF : F ∈ G.crossingChangeInitialPartners C t x z) :
    b ∉ F.toRectangleDecomposition.commonSideColumns := by
  obtain ⟨-, D, -, hrecut⟩ := (G.mem_crossingChangeInitialPartners C t F).mp hF
  have hcommon := hrecut.isRecutOfLeftEqLeft (D.first.left_eq.trans D.second.left_eq.symm)
  simpa only [D.first.left_eq] using hcommon.first_left_notMem_commonSideColumns

/-- A terminal--initial partner has `b = finRotate n C.column` as a common side column of its two
rectangles. -/
private theorem finRotate_mem_commonSideColumns_of_mem_crossingChangeTerminalInitialPartners
    {x z : GridState n} {F : GridHexagonCompositeDecomposition a C.turnRow t x z}
    (hF : F ∈ G.crossingChangeTerminalInitialPartners C t x z) :
    b ∈ F.toRectangleDecomposition.commonSideColumns := by
  obtain ⟨-, D, -, hDF⟩ := (G.mem_crossingChangeTerminalInitialPartners C t F).mp hF
  rw [← hDF, GridRectangleDecomposition.mem_commonSideColumns]
  simp [GridRectangleBetween.mem_sideColumns, D.first.right_eq, D.second.left_eq]

/-- An initial--terminal partner has `b = finRotate n C.column` as a common side column of its two
rectangles. -/
private theorem finRotate_mem_commonSideColumns_of_mem_crossingChangeInitialTerminalPartners
    {x z : GridState n} {F : GridHexagonCompositeDecomposition a C.turnRow t x z}
    (hF : F ∈ G.crossingChangeInitialTerminalPartners C t x z) :
    b ∈ F.toRectangleDecomposition.commonSideColumns := by
  obtain ⟨-, D, -, hDF⟩ := (G.mem_crossingChangeInitialTerminalPartners C t F).mp hF
  rw [← hDF, GridRectangleDecomposition.mem_commonSideColumns]
  simp [GridRectangleBetween.mem_sideColumns, D.first.left_eq, D.second.right_eq]

/-- The terminal--terminal and initial--initial partner finsets are disjoint. -/
theorem disjoint_crossingChangeTerminalPartners_crossingChangeInitialPartners
    {x z : GridState n} :
    Disjoint (G.crossingChangeTerminalPartners C t x z)
      (G.crossingChangeInitialPartners C t x z) := by
  rw [Finset.disjoint_left]
  intro F hT hI
  obtain ⟨-, D₁, hD₁, hrec₁⟩ := (G.mem_crossingChangeTerminalPartners C t F).mp hT
  obtain ⟨-, D₂, hD₂, hrec₂⟩ := (G.mem_crossingChangeInitialPartners C t F).mp hI
  obtain ⟨hP₁, hQ₁⟩ := (G.mem_crossingChangeTerminalPairs C t D₁).mp hD₁
  obtain ⟨hP₂, hQ₂⟩ := (G.mem_crossingChangeInitialPairs C t D₂).mp hD₂
  have hrect := hrec₁.eq_of_isRecut hrec₂
    ((G.mem_pentagons D₁.first).mp hP₁).1
    (((G.swapColumns a b).mem_pentagons (C := C.withTurnRow t) D₁.second).mp hQ₁).1
    ((G.mem_initialPentagons D₂.first).mp hP₂).1
    (((G.swapColumns a b).mem_initialPentagons (C := C.withTurnRow t) D₂.second).mp hQ₂).1
  have hleft : D₁.first.left = D₂.first.left :=
    congrArg (fun R : GridRectangleDecomposition x z => R.first.left) hrect
  exact D₁.first.left_ne_right (hleft.trans (D₂.first.left_eq.trans D₁.first.right_eq.symm))

/-- The terminal--initial and initial--terminal partner finsets are disjoint. -/
theorem disjoint_crossingChangeTerminalInitialPartners_crossingChangeInitialTerminalPartners
    {x z : GridState n} :
    Disjoint (G.crossingChangeTerminalInitialPartners C t x z)
      (G.crossingChangeInitialTerminalPartners C t x z) := by
  rw [Finset.disjoint_left]
  intro F hTI hIT
  obtain ⟨-, D₁, -, hDF₁⟩ := (G.mem_crossingChangeTerminalInitialPartners C t F).mp hTI
  obtain ⟨-, D₂, -, hDF₂⟩ := (G.mem_crossingChangeInitialTerminalPartners C t F).mp hIT
  have hleft : D₁.first.left = D₂.first.left :=
    congrArg (fun R : GridRectangleDecomposition x z => R.first.left) (hDF₁.trans hDF₂.symm)
  exact D₁.first.left_ne_right (hleft.trans (D₂.first.left_eq.trans D₁.first.right_eq.symm))

open scoped Classical in
/-- The same-side partner finsets are disjoint from the mixed-side partner finsets: the replaced
grid line `b` is a common side column of the latter, never of the former. -/
theorem disjoint_crossingChangeSameSidePartners_crossingChangeMixedSidePartners
    {x z : GridState n} :
    Disjoint
      (G.crossingChangeTerminalPartners C t x z ∪ G.crossingChangeInitialPartners C t x z)
      (G.crossingChangeTerminalInitialPartners C t x z ∪
        G.crossingChangeInitialTerminalPartners C t x z) := by
  rw [Finset.disjoint_left]
  intro F hS hM
  have hnot : b ∉ F.toRectangleDecomposition.commonSideColumns := by
    rcases Finset.mem_union.mp hS with hS | hS
    · exact G.finRotate_notMem_commonSideColumns_of_mem_crossingChangeTerminalPartners C t hS
    · exact G.finRotate_notMem_commonSideColumns_of_mem_crossingChangeInitialPartners C t hS
  have hmem : b ∈ F.toRectangleDecomposition.commonSideColumns := by
    rcases Finset.mem_union.mp hM with hM | hM
    · exact G.finRotate_mem_commonSideColumns_of_mem_crossingChangeTerminalInitialPartners C t hM
    · exact G.finRotate_mem_commonSideColumns_of_mem_crossingChangeInitialTerminalPartners C t hM
  exact hnot hmem

open scoped Classical in
/-- Off the diagonal (`z ≠ x`), when the crossing-change annulus squares carry no `X`-marking,
every unpaired hexagon composite belongs to one of the four pentagon-partner finsets. -/
theorem crossingChangeUnpairedHexagonComposites_eq_union
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hzx : z ≠ x) :
    G.crossingChangeUnpairedHexagonComposites C t x z =
      (G.crossingChangeTerminalPartners C t x z ∪ G.crossingChangeInitialPartners C t x z) ∪
        (G.crossingChangeTerminalInitialPartners C t x z ∪
          G.crossingChangeInitialTerminalPartners C t x z) := by
  refine Finset.Subset.antisymm (fun F hF => ?_) (Finset.union_subset
    (Finset.union_subset (G.crossingChangeTerminalPartners_subset C t x z)
      (G.crossingChangeInitialPartners_subset C t x z))
    (Finset.union_subset (G.crossingChangeTerminalInitialPartners_subset C t x z)
      (G.crossingChangeInitialTerminalPartners_subset C t x z)))
  obtain ⟨⟨m, P, Q⟩, ⟨hP, hQ⟩, hcase⟩ :=
    exists_pentagonPair_of_mem_crossingChangeUnpairedHexagonComposites hX hzx hF
  simp only [Finset.mem_union]
  cases P with
  | inl P =>
    cases Q with
    | inl Q =>
      rcases hcase with ⟨-, hrec⟩ | ⟨hside, -⟩
      · exact Or.inl (Or.inl ((G.mem_crossingChangeTerminalPartners C t F).mpr
          ⟨hF, ⟨m, P, Q⟩, (G.mem_crossingChangeTerminalPairs C t _).mpr
            ⟨by simpa using hP, by simpa using hQ⟩,
            by simpa [GridPentagonPairDecomposition.toRectangleDecomposition] using hrec⟩))
      · simp at hside
    | inr Q =>
      rcases hcase with ⟨hside, -⟩ | ⟨-, hrect⟩
      · simp at hside
      · exact Or.inr (Or.inl ((G.mem_crossingChangeTerminalInitialPartners C t F).mpr
          ⟨hF, ⟨m, P, Q⟩, (G.mem_crossingChangeTerminalInitialPairs C t _).mpr
            ⟨by simpa using hP, by simpa using hQ⟩,
            by simpa [GridPentagonPairDecomposition.toRectangleDecomposition] using hrect⟩))
  | inr P =>
    cases Q with
    | inl Q =>
      rcases hcase with ⟨hside, -⟩ | ⟨-, hrect⟩
      · simp at hside
      · exact Or.inr (Or.inr ((G.mem_crossingChangeInitialTerminalPartners C t F).mpr
          ⟨hF, ⟨m, P, Q⟩, (G.mem_crossingChangeInitialTerminalPairs C t _).mpr
            ⟨by simpa using hP, by simpa using hQ⟩,
            by simpa [GridPentagonPairDecomposition.toRectangleDecomposition] using hrect⟩))
    | inr Q =>
      rcases hcase with ⟨-, hrec⟩ | ⟨hside, -⟩
      · exact Or.inl (Or.inr ((G.mem_crossingChangeInitialPartners C t F).mpr
          ⟨hF, ⟨m, P, Q⟩, (G.mem_crossingChangeInitialPairs C t _).mpr
            ⟨by simpa using hP, by simpa using hQ⟩,
            by simpa [GridPentagonPairDecomposition.toRectangleDecomposition] using hrec⟩))
      · simp at hside

/-- **Total unpaired-composite weight equals the round-trip pentagon-coefficient sum.** Off the
diagonal (`z ≠ x`), for distinct turn rows and with no `X`-marking in the crossing-change annulus,
the unpaired hexagon composites have the same total polynomial weight as the round-trip product of
pentagon coefficients over every commutative semiring. -/
theorem sum_crossingChangeUnpairedHexagonComposites_eq_sum_pentagonCoefficient
    (R : Type*) [CommSemiring R] (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {x z : GridState n} (hzx : z ≠ x) :
    ∑ F ∈ G.crossingChangeUnpairedHexagonComposites C t x z,
        G.crossingChangeHexagonCompositeWeight C t R F =
      ∑ y : GridState n,
        MvPolynomial.rename (Equiv.swap a b) (G.commutationPentagonCoefficient R C x y) *
          (G.swapColumns a b).commutationPentagonCoefficient R (C.withTurnRow t) y z := by
  classical
  rw [G.crossingChangeUnpairedHexagonComposites_eq_union C t hX hzx,
    Finset.sum_union
      (G.disjoint_crossingChangeSameSidePartners_crossingChangeMixedSidePartners C t),
    Finset.sum_union (G.disjoint_crossingChangeTerminalPartners_crossingChangeInitialPartners C t),
    Finset.sum_union
      (G.disjoint_crossingChangeTerminalInitialPartners_crossingChangeInitialTerminalPartners C t),
    ← G.sum_rename_pentagonCoefficient_mul_eq_sum_crossingChangeTerminalPartners C t R hX hzx,
    ← G.sum_rename_initialPentagonCoefficient_mul_eq_sum_crossingChangeInitialPartners C t R hX hzx,
    ← G.sum_rename_pentagonCoefficient_mul_eq_sum_crossingChangeTerminalInitialPartners
        C t R hst hX hzx,
    ← G.sum_rename_initialPentagonCoefficient_mul_eq_sum_crossingChangeInitialTerminalPartners
        C t R hst hX hzx]
  simp_rw [commutationPentagonCoefficient_def, map_add, add_mul, mul_add, Finset.sum_add_distrib]
  ac_rfl

/-! ### The crossing-change homotopy equations in characteristic two -/

section CharTwo

variable (R : Type*) [CommSemiring R] [CharP R 2]

/-- **The crossing-change homotopy equation.** If the turn rows `C.turnRow` and `t` differ and the
annulus squares carry no `X`-marking, then over any commutative semiring of characteristic two the
hexagon-counting map `H = G.crossingChangeHomotopy R C t` satisfies
`∂(H(c)) + H(∂(c)) = w • c + Ψ(Φ(c))` on every chain `c`, where `w` is the annulus weight. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq
    (hst : C.turnRow ≠ t) (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    (c : GridChainMinus R n) :
    G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
        G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
      G.crossingChangeAnnulusWeight R C t • c +
        (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c) :=
  (unblockedDifferential_crossingChangeHomotopy_add_eq_iff_unpaired R hst hX).mpr
    (fun _ _ hxz => G.sum_crossingChangeUnpairedHexagonComposites_eq_sum_pentagonCoefficient
      C t R hst hX hxz.symm) c

/-- **The crossing-change homotopy equation for markings in cyclic order `O_b, O_a, X_b, X_a`.**
If the segments of the adjacent columns `a` and `b = finRotate n a` interleave with `O_a` on the
arc of column `b`, and the crossing-change maps turn in the rows of `O_a` and `X_b`, then over any
commutative semiring of characteristic two `∂(H(c)) + H(∂(c)) = V_b • c + Ψ(Φ(c))`. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq_of_mem_columnArc
    (h : G.ColumnsInterleaving a b) (hO : G.O a ∈ G.columnArc b)
    (hs : C.turnRow = G.O a) (ht : t = G.X b) (c : GridChainMinus R n) :
    G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
        G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
      (MvPolynomial.X b : MvPolynomial (Fin n) R) • c +
        (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c) :=
  (unblockedDifferential_crossingChangeHomotopy_add_eq_iff_unpaired_of_mem_columnArc
    R h hO hs ht).mpr
    (fun _ _ hxz => G.sum_crossingChangeUnpairedHexagonComposites_eq_sum_pentagonCoefficient C t R
      (by rw [hs, ht]; exact ((columnsInterleaving_iff_not_columnsNoninterleaving G _ _).mp h).2.1)
      (disjoint_crossingChangeAnnulusSquares_XSet_of_mem_columnArc h hO hs ht) hxz.symm) c

/-- **The crossing-change homotopy equation for markings in cyclic order `O_b, X_a, X_b, O_a`.**
If the segments of the adjacent columns `a` and `b = finRotate n a` interleave with `O_a` off the
arc of column `b`, and the crossing-change maps turn in the rows of `X_a` and `O_b`, then over any
commutative semiring of characteristic two `∂(H(c)) + H(∂(c)) = V_a • c + Ψ(Φ(c))`. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq_of_notMem_columnArc
    (h : G.ColumnsInterleaving a b) (hO : G.O a ∉ G.columnArc b)
    (hs : C.turnRow = G.X a) (ht : t = G.O b) (c : GridChainMinus R n) :
    G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
        G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
      (MvPolynomial.X a : MvPolynomial (Fin n) R) • c +
        (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c) :=
  (unblockedDifferential_crossingChangeHomotopy_add_eq_iff_unpaired_of_notMem_columnArc
    R h hO hs ht).mpr
    (fun _ _ hxz => G.sum_crossingChangeUnpairedHexagonComposites_eq_sum_pentagonCoefficient C t R
      (by rw [hs, ht]; exact ((columnsInterleaving_iff_not_columnsNoninterleaving G _ _).mp h).2.2)
      (disjoint_crossingChangeAnnulusSquares_XSet_of_notMem_columnArc h hO hs ht) hxz.symm) c

/-- On a cycle `z` of `GC⁻(G)`, the round trip `Ψ ∘ Φ` equals `w • z` up to the boundary of
`H(z)`. -/
theorem commutationMap_withTurnRow_commutationMap_of_mem_ker
    (hst : C.turnRow ≠ t) (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet)
    {z : GridChainMinus R n} (hz : z ∈ LinearMap.ker (G.unblockedDifferential R)) :
    (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C z) =
      G.crossingChangeAnnulusWeight R C t • z +
        G.unblockedDifferential R (G.crossingChangeHomotopy R C t z) := by
  have h := G.unblockedDifferential_crossingChangeHomotopy_add_eq C t R hst hX z
  rw [LinearMap.mem_ker.mp hz, map_zero, add_zero] at h
  rw [h, ← add_assoc, add_self_eq_zero_of_charTwo (MvPolynomial (Fin n) R) _, zero_add]

/-- On a cycle `z` of `GC⁻(G)` with `O_a` on the arc of column `b`, the round trip `Ψ ∘ Φ` equals
`V_b • z` up to the boundary of `H(z)`. -/
theorem commutationMap_withTurnRow_commutationMap_of_mem_ker_of_mem_columnArc
    (h : G.ColumnsInterleaving a b) (hO : G.O a ∈ G.columnArc b)
    (hs : C.turnRow = G.O a) (ht : t = G.X b)
    {z : GridChainMinus R n} (hz : z ∈ LinearMap.ker (G.unblockedDifferential R)) :
    (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C z) =
      (MvPolynomial.X b : MvPolynomial (Fin n) R) • z +
        G.unblockedDifferential R (G.crossingChangeHomotopy R C t z) := by
  have hEq := G.unblockedDifferential_crossingChangeHomotopy_add_eq_of_mem_columnArc
    C t R h hO hs ht z
  rw [LinearMap.mem_ker.mp hz, map_zero, add_zero] at hEq
  rw [hEq, ← add_assoc, add_self_eq_zero_of_charTwo (MvPolynomial (Fin n) R) _, zero_add]

/-- On a cycle `z` of `GC⁻(G)` with `O_a` off the arc of column `b`, the round trip `Ψ ∘ Φ` equals
`V_a • z` up to the boundary of `H(z)`. -/
theorem commutationMap_withTurnRow_commutationMap_of_mem_ker_of_notMem_columnArc
    (h : G.ColumnsInterleaving a b) (hO : G.O a ∉ G.columnArc b)
    (hs : C.turnRow = G.X a) (ht : t = G.O b)
    {z : GridChainMinus R n} (hz : z ∈ LinearMap.ker (G.unblockedDifferential R)) :
    (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C z) =
      (MvPolynomial.X a : MvPolynomial (Fin n) R) • z +
        G.unblockedDifferential R (G.crossingChangeHomotopy R C t z) := by
  have hEq := G.unblockedDifferential_crossingChangeHomotopy_add_eq_of_notMem_columnArc
    C t R h hO hs ht z
  rw [LinearMap.mem_ker.mp hz, map_zero, add_zero] at hEq
  rw [hEq, ← add_assoc, add_self_eq_zero_of_charTwo (MvPolynomial (Fin n) R) _, zero_add]

end CharTwo

end TauCeti.GridDiagram
