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

## Main definitions

* `TauCeti.GridDiagram.columnTurnPentagons` and `TauCeti.GridDiagram.columnTurnPentagonWeight`:
  the counted pentagons of both turn-side kinds at an arbitrary column turn, and their weights.
* `TauCeti.GridDiagram.crossingChangePentagonPairDecompositions` and
  `TauCeti.GridDiagram.crossingChangePentagonPairWeight`: the counted pentagon pairs of `Ψ ∘ Φ`
  and their weights.

## Main results

* `sum_crossingChangeUnpairedHexagonCompositeWeight_eq_sum_crossingChangePentagonPairWeight` and
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
-/

public section

namespace TauCeti.GridDiagram

open MvPolynomial

variable {n : ℕ} (G : GridDiagram n) (C : ColumnTurn n) (t : Fin n)

local notation "a" => C.column
local notation "b" => finRotate n C.column

/-! ### Pentagon pairs for a pair of column turns -/

/-- The pentagons counted by the commutation map of an arbitrary column turn `C`, of both turn-side
kinds (the `ColumnTurn` counterpart of `GridDiagram.commutationPentagons` on
`ColumnCommutationData`). -/
noncomputable def columnTurnPentagons (x y : GridState n) :
    Finset (GridCommutationPentagonBetween a C.turnRow x y) :=
  (G.pentagons C x y).disjSum (G.initialPentagons C x y)

/-- The counted pentagons of a column turn are the disjoint union of its terminal-side and
initial-side pentagons. -/
theorem columnTurnPentagons_def (x y : GridState n) :
    G.columnTurnPentagons C x y = (G.pentagons C x y).disjSum (G.initialPentagons C x y) :=
  (rfl)

/-- A terminal-side pentagon belongs to `columnTurnPentagons` exactly when it is counted. -/
@[simp]
theorem inl_mem_columnTurnPentagons {x y : GridState n} (P : GridPentagonBetween a C.turnRow x y) :
    Sum.inl P ∈ G.columnTurnPentagons C x y ↔ P ∈ G.pentagons C x y :=
  Finset.inl_mem_disjSum

/-- An initial-side pentagon belongs to `columnTurnPentagons` exactly when it is counted. -/
@[simp]
theorem inr_mem_columnTurnPentagons {x y : GridState n}
    (P : GridInitialPentagonBetween a C.turnRow x y) :
    Sum.inr P ∈ G.columnTurnPentagons C x y ↔ P ∈ G.initialPentagons C x y :=
  Finset.inr_mem_disjSum

/-- The polynomial weight of a commutation pentagon of either turn-side kind at a column turn. -/
noncomputable def columnTurnPentagonWeight (R : Type*) [CommSemiring R] {x y : GridState n}
    (P : GridCommutationPentagonBetween a C.turnRow x y) : MvPolynomial (Fin n) R :=
  P.elim (G.pentagonWeight R C) (G.initialPentagonWeight R C)

/-- The weight of a terminal-side pentagon at a column turn. -/
@[simp]
theorem columnTurnPentagonWeight_inl (R : Type*) [CommSemiring R] {x y : GridState n}
    (P : GridPentagonBetween a C.turnRow x y) :
    G.columnTurnPentagonWeight C R (Sum.inl P) = G.pentagonWeight R C P :=
  (rfl)

/-- The weight of an initial-side pentagon at a column turn. -/
@[simp]
theorem columnTurnPentagonWeight_inr (R : Type*) [CommSemiring R] {x y : GridState n}
    (P : GridInitialPentagonBetween a C.turnRow x y) :
    G.columnTurnPentagonWeight C R (Sum.inr P) = G.initialPentagonWeight R C P :=
  (rfl)

/-- The matrix coefficient of the commutation map of `C` is the sum of the weights of its counted
pentagons of both turn-side kinds. -/
theorem commutationPentagonCoefficient_eq_sum_columnTurnPentagonWeight
    (R : Type*) [CommSemiring R] (x y : GridState n) :
    G.commutationPentagonCoefficient R C x y =
      ∑ P ∈ G.columnTurnPentagons C x y, G.columnTurnPentagonWeight C R P := by
  rw [G.commutationPentagonCoefficient_def R C, G.pentagonCoefficient_def R C x y,
    G.initialPentagonCoefficient_def R C x y, columnTurnPentagons, Finset.sum_disjSum]
  simp only [columnTurnPentagonWeight_inl, columnTurnPentagonWeight_inr]

/-- The pairs of a counted pentagon of `G` at `C` followed by a counted pentagon of
`G.swapColumns a b` at `C.withTurnRow t`. -/
noncomputable def crossingChangePentagonPairDecompositions (x z : GridState n) :
    Finset (GridPentagonPairDecomposition a C.turnRow a t x z) :=
  GridTwoStepDecomposition.decompositionsOf (G.columnTurnPentagons C)
    ((G.swapColumns a b).columnTurnPentagons (C.withTurnRow t)) x z

/-- The counted crossing-change pentagon pairs are the two-step decompositions of the counted
pentagons at `C` and `C.withTurnRow t`. -/
theorem crossingChangePentagonPairDecompositions_def (x z : GridState n) :
    G.crossingChangePentagonPairDecompositions C t x z =
      GridTwoStepDecomposition.decompositionsOf (G.columnTurnPentagons C)
        ((G.swapColumns a b).columnTurnPentagons (C.withTurnRow t)) x z :=
  (rfl)

/-- Membership in `crossingChangePentagonPairDecompositions` is countedness of both pentagons. -/
@[simp]
theorem mem_crossingChangePentagonPairDecompositions {x z : GridState n}
    (D : GridPentagonPairDecomposition a C.turnRow a t x z) :
    D ∈ G.crossingChangePentagonPairDecompositions C t x z ↔
      D.first ∈ G.columnTurnPentagons C x D.middle ∧
        D.second ∈ (G.swapColumns a b).columnTurnPentagons (C.withTurnRow t) D.middle z := by
  classical
  simp only [crossingChangePentagonPairDecompositions,
    GridTwoStepDecomposition.mem_decompositionsOf]

variable {G C t} in
/-- Both underlying rectangles of a counted crossing-change pentagon pair are empty. -/
theorem isEmpty_of_mem_crossingChangePentagonPairDecompositions {x z : GridState n}
    {D : GridPentagonPairDecomposition a C.turnRow a t x z}
    (hD : D ∈ G.crossingChangePentagonPairDecompositions C t x z) :
    D.toRectangleDecomposition.first.IsEmpty ∧ D.toRectangleDecomposition.second.IsEmpty := by
  obtain ⟨hP, hQ⟩ := (G.mem_crossingChangePentagonPairDecompositions C t D).mp hD
  rcases D with ⟨m, P | P, Q | Q⟩ <;>
    simp only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inl,
      GridCommutationPentagonBetween.toGridRectangleBetween_inr]
  · exact ⟨((G.mem_pentagons P).mp ((G.inl_mem_columnTurnPentagons C P).mp hP)).1,
      (((G.swapColumns a b).mem_pentagons (C := C.withTurnRow t) Q).mp
        (((G.swapColumns a b).inl_mem_columnTurnPentagons (C.withTurnRow t) Q).mp hQ)).1⟩
  · exact ⟨((G.mem_pentagons P).mp ((G.inl_mem_columnTurnPentagons C P).mp hP)).1,
      (((G.swapColumns a b).mem_initialPentagons (C := C.withTurnRow t) Q).mp
        (((G.swapColumns a b).inr_mem_columnTurnPentagons (C.withTurnRow t) Q).mp hQ)).1⟩
  · exact ⟨((G.mem_initialPentagons P).mp ((G.inr_mem_columnTurnPentagons C P).mp hP)).1,
      (((G.swapColumns a b).mem_pentagons (C := C.withTurnRow t) Q).mp
        (((G.swapColumns a b).inl_mem_columnTurnPentagons (C.withTurnRow t) Q).mp hQ)).1⟩
  · exact ⟨((G.mem_initialPentagons P).mp ((G.inr_mem_columnTurnPentagons C P).mp hP)).1,
      (((G.swapColumns a b).mem_initialPentagons (C := C.withTurnRow t) Q).mp
        (((G.swapColumns a b).inr_mem_columnTurnPentagons (C.withTurnRow t) Q).mp hQ)).1⟩

/-- The polynomial weight of a crossing-change pentagon pair: the renamed weight of the first
pentagon times the weight of the second on the column-swapped diagram. -/
noncomputable def crossingChangePentagonPairWeight (R : Type*) [CommSemiring R] {x z : GridState n}
    (D : GridPentagonPairDecomposition a C.turnRow a t x z) : MvPolynomial (Fin n) R :=
  rename (Equiv.swap a b) (G.columnTurnPentagonWeight C R D.first) *
    (G.swapColumns a b).columnTurnPentagonWeight (C.withTurnRow t) R D.second

/-- The weight of a crossing-change pentagon pair is the product of the renamed first weight and
the second weight. -/
theorem crossingChangePentagonPairWeight_def (R : Type*) [CommSemiring R] {x z : GridState n}
    (D : GridPentagonPairDecomposition a C.turnRow a t x z) :
    G.crossingChangePentagonPairWeight C t R D =
      rename (Equiv.swap a b) (G.columnTurnPentagonWeight C R D.first) *
        (G.swapColumns a b).columnTurnPentagonWeight (C.withTurnRow t) R D.second :=
  (rfl)

/-- The matrix product of the commutation coefficients of `C` and `C.withTurnRow t` equals the sum
of the weights of the counted pentagon pairs. -/
theorem sum_rename_commutationPentagonCoefficient_mul_commutationPentagonCoefficient_withTurnRow
    (R : Type*) [CommSemiring R] (x z : GridState n) :
    ∑ y : GridState n,
        rename (Equiv.swap a b) (G.commutationPentagonCoefficient R C x y) *
          (G.swapColumns a b).commutationPentagonCoefficient R (C.withTurnRow t) y z =
      ∑ D ∈ G.crossingChangePentagonPairDecompositions C t x z,
        G.crossingChangePentagonPairWeight C t R D := by
  simp_rw [G.commutationPentagonCoefficient_eq_sum_columnTurnPentagonWeight C R,
    (G.swapColumns a b).commutationPentagonCoefficient_eq_sum_columnTurnPentagonWeight
      (C.withTurnRow t) R,
    map_sum, Finset.sum_mul_sum]
  exact (GridTwoStepDecomposition.sum_decompositionsOf (G.columnTurnPentagons C)
    ((G.swapColumns a b).columnTurnPentagons (C.withTurnRow t))
    (fun _ P Q => rename (Equiv.swap a b) (G.columnTurnPentagonWeight C R P) *
      (G.swapColumns a b).columnTurnPentagonWeight (C.withTurnRow t) R Q)).symm

/-! ### Matching unpaired composites with pentagon pairs -/

section Matching

variable {G C t}

/-- The replaced grid line `b = finRotate n a` is a common side of the two rectangles of every
crossing-change pentagon pair. -/
private theorem finRotate_mem_commonSideColumns_of_crossingChangePentagonPair {x z : GridState n}
    (D : GridPentagonPairDecomposition a C.turnRow a t x z) :
    b ∈ D.toRectangleDecomposition.commonSideColumns := by
  rcases D with ⟨m, P | P, Q | Q⟩
  · simp [P.right_eq, Q.right_eq]
  · simp [P.right_eq, Q.left_eq]
  · simp [P.left_eq, Q.right_eq]
  · simp [P.left_eq, Q.left_eq]

/-- The recut of a same-side pentagon pair never has the replaced grid line `b` as a common side of
its two rectangles. -/
private theorem finRotate_notMem_commonSideColumns_of_sameSide_isRecut {x z : GridState n}
    {D : GridPentagonPairDecomposition a C.turnRow a t x z} {E : GridRectangleDecomposition x z}
    (hside : D.first.isLeft = D.second.isLeft) (hrecut : D.toRectangleDecomposition.IsRecut E) :
    b ∉ E.commonSideColumns := by
  rcases D with ⟨m, P | P, Q | Q⟩
  · have hcommon := hrecut.isRecutOfRightEqRight (by
      simp only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inl, P.right_eq, Q.right_eq])
    intro hb
    apply hcommon.first_right_notMem_commonSideColumns
    simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inl, P.right_eq] using hb
  · simp at hside
  · simp at hside
  · have hcommon := hrecut.isRecutOfLeftEqLeft (by
      simp only [GridPentagonPairDecomposition.toRectangleDecomposition,
        GridCommutationPentagonBetween.toGridRectangleBetween_inr, P.left_eq, Q.left_eq])
    intro hb
    apply hcommon.first_left_notMem_commonSideColumns
    simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inr, P.left_eq] using hb

/-- Each counted off-diagonal pentagon pair has an unpaired hexagon-composite partner of the same
weight: its recut in the same-side case, or the composite with the same rectangles in the
mixed-side case. -/
private theorem exists_unpairedPartner_of_mem_crossingChangePentagonPairDecompositions
    (R : Type*) [CommSemiring R] (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) {x z : GridState n} (hzx : z ≠ x)
    {D : GridPentagonPairDecomposition a C.turnRow a t x z}
    (hD : D ∈ G.crossingChangePentagonPairDecompositions C t x z) :
    ∃ F ∈ G.crossingChangeUnpairedHexagonComposites C t x z,
      ((D.first.isLeft = D.second.isLeft ∧
          D.toRectangleDecomposition.IsRecut F.toRectangleDecomposition) ∨
        (D.first.isLeft ≠ D.second.isLeft ∧
          D.toRectangleDecomposition = F.toRectangleDecomposition)) ∧
        G.crossingChangePentagonPairWeight C t R D =
          G.crossingChangeHexagonCompositeWeight C t R F := by
  obtain ⟨hP, hQ⟩ := (G.mem_crossingChangePentagonPairDecompositions C t D).mp hD
  rcases D with ⟨m, P | P, Q | Q⟩
  · obtain ⟨⟨F, ⟨hF, hrecut⟩, -⟩, hw⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_terminalPentagonPair R hX P Q
        ((G.inl_mem_columnTurnPentagons C P).mp hP)
        (((G.swapColumns a b).inl_mem_columnTurnPentagons (C.withTurnRow t) Q).mp hQ) hzx
    refine ⟨F, hF, Or.inl ⟨rfl, ?_⟩, (hw F hF hrecut).symm⟩
    simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inl] using hrecut
  · obtain ⟨F, ⟨hF, hFD, hw⟩, -⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_terminalInitialPentagonPair R hst hX
        P Q ((G.inl_mem_columnTurnPentagons C P).mp hP)
        (((G.swapColumns a b).inr_mem_columnTurnPentagons (C.withTurnRow t) Q).mp hQ) hzx
    refine ⟨F, hF, Or.inr ⟨by simp, ?_⟩, hw.symm⟩
    simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inl,
      GridCommutationPentagonBetween.toGridRectangleBetween_inr] using hFD.symm
  · obtain ⟨F, ⟨hF, hFD, hw⟩, -⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_initialTerminalPentagonPair R hst hX
        P Q ((G.inr_mem_columnTurnPentagons C P).mp hP)
        (((G.swapColumns a b).inl_mem_columnTurnPentagons (C.withTurnRow t) Q).mp hQ) hzx
    refine ⟨F, hF, Or.inr ⟨by simp, ?_⟩, hw.symm⟩
    simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inl,
      GridCommutationPentagonBetween.toGridRectangleBetween_inr] using hFD.symm
  · obtain ⟨⟨F, ⟨hF, hrecut⟩, -⟩, hw⟩ :=
      existsUnique_crossingChangeUnpairedHexagonComposite_of_initialPentagonPair R hX P Q
        ((G.inr_mem_columnTurnPentagons C P).mp hP)
        (((G.swapColumns a b).inr_mem_columnTurnPentagons (C.withTurnRow t) Q).mp hQ) hzx
    refine ⟨F, hF, Or.inl ⟨rfl, ?_⟩, (hw F hF hrecut).symm⟩
    simpa only [GridPentagonPairDecomposition.toRectangleDecomposition,
      GridCommutationPentagonBetween.toGridRectangleBetween_inr] using hrecut

/-- **Off-diagonal matching for a crossing change.** If the turn rows `C.turnRow` and `t` differ
and the annulus squares carry no `X`-marking, then for distinct grid states `x` and `z` the
unpaired hexagon composites and the counted pentagon pairs have equal total polynomial weight over
every commutative semiring. -/
theorem sum_crossingChangeUnpairedHexagonCompositeWeight_eq_sum_crossingChangePentagonPairWeight
    (R : Type*) [CommSemiring R] (hst : C.turnRow ≠ t)
    (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) {x z : GridState n} (hxz : x ≠ z) :
    ∑ F ∈ G.crossingChangeUnpairedHexagonComposites C t x z,
        G.crossingChangeHexagonCompositeWeight C t R F =
      ∑ D ∈ G.crossingChangePentagonPairDecompositions C t x z,
        G.crossingChangePentagonPairWeight C t R D := by
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
    (fun _ hD => exists_unpairedPartner_of_mem_crossingChangePentagonPairDecompositions R hst hX
      hzx hD)
    (fun D hD E hE F _ hDF hEF => ?_)
    (fun D hD F hF F' hF' hDF hDF' => ?_)
    (fun F hF => ?_)
  · rcases hDF with ⟨hsD, hrecD⟩ | ⟨_, hEqD⟩ <;> rcases hEF with ⟨hsE, hrecE⟩ | ⟨_, hEqE⟩
    · obtain ⟨hfD, hsecD⟩ := isEmpty_of_mem_crossingChangePentagonPairDecompositions hD
      obtain ⟨hfE, hsecE⟩ := isEmpty_of_mem_crossingChangePentagonPairDecompositions hE
      exact GridPentagonPairDecomposition.toRectangleDecomposition_injective
        (hrecD.eq_of_isRecut hrecE hfD hsecD hfE hsecE)
    · exact absurd (hEqE ▸ finRotate_mem_commonSideColumns_of_crossingChangePentagonPair E)
        (finRotate_notMem_commonSideColumns_of_sameSide_isRecut hsD hrecD)
    · exact absurd (hEqD ▸ finRotate_mem_commonSideColumns_of_crossingChangePentagonPair D)
        (finRotate_notMem_commonSideColumns_of_sameSide_isRecut hsE hrecE)
    · exact GridPentagonPairDecomposition.toRectangleDecomposition_injective
        (hEqD.trans hEqE.symm)
  · apply injOn_toRectangleDecomposition_crossingChangeHexagonCompositeDecompositions hX x z
      (hcomp hF) (hcomp hF')
    rcases hDF with ⟨hs, hrec⟩ | ⟨hns, hEq⟩ <;> rcases hDF' with ⟨hs', hrec'⟩ | ⟨hns', hEq'⟩
    · obtain ⟨hf, hsec⟩ := isEmpty_of_mem_crossingChangePentagonPairDecompositions hD
      exact (D.toRectangleDecomposition.existsUnique_isRecut
        (GridRectangleDecomposition.hasOneCommonSide_of_isRecut hrec) hf hsec).unique hrec hrec'
    · exact absurd hs hns'
    · exact absurd hs' hns
    · exact hEq.symm.trans hEq'
  · obtain ⟨D, ⟨hP, hQ⟩, hr⟩ := exists_pentagonPair_of_mem_crossingChangeUnpairedHexagonComposites
      hX hzx hF
    exact ⟨D, (G.mem_crossingChangePentagonPairDecompositions C t D).mpr ⟨hP, hQ⟩, hr⟩

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
  rw [G.sum_rename_commutationPentagonCoefficient_mul_commutationPentagonCoefficient_withTurnRow
    C t R,
    sum_crossingChangeUnpairedHexagonCompositeWeight_eq_sum_crossingChangePentagonPairWeight
      R hst hX hxz]

end Matching

/-! ### The crossing-change homotopy equation -/

section Equation

variable {G C t} (R : Type*) [CommSemiring R] [CharP R 2]

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
