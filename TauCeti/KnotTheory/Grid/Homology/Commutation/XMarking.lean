/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.Commutation.Basic
public import TauCeti.KnotTheory.Grid.Homology.NonTorsion

/-!
# The commutation map on the `X`-marking state

The `X`-marking state `G.X` of a grid diagram, whose point in each column is the lower-left corner
of the `X`-marked square, is the grid state `x⁻(G)` of Ozsváth--Szabó--Thurston. It is a cycle of
the unblocked grid complex `GC⁻`, and its class `XMarkingClass` in `GH⁻` is their class `λ⁻(G)`,
which they show to be an invariant of the Legendrian knot the diagram presents. This file shows
that the pentagon-counting commutation map `Φ` of a column commutation carries `x⁻(G)` to
`x⁻(G')`, where `G'` is the commuted diagram, so that the induced map on `GH⁻` carries `λ⁻(G)` to
`λ⁻(G')`. Nothing about Legendrian knots is formalised here.

Let `a` and `b = finRotate n a` be the commuted columns, and let the turn point lie in square
row `s`. A pentagon turning on its initial side starts at the point of `G.X` on the line `b`, the
lower-left corner of the `X`-marked square of column `b`, and carries that marking unless `s` is
its row; so if the turn row is not the row of `X_b`, no such pentagon from `G.X` is counted
(`initialPentagons_X_eq_empty`). A pentagon turning on its terminal side with initial side `j`
starts at the lower-left corner of the `X`-marked square of column `j`, and carries that marking
unless `j = a`, where the marking lies below the turn point; so every counted one ends at
`G.X.swapColumns a b`, which is `G'.X` (`pentagons_X_eq_empty`). For validated commutation data
the pentagon with initial side `a` is one column wide, hence empty, and it carries neither an
`X`-marking nor an `O`-marking; for the `O`-marking of column `b` this uses that the two columns
do not interleave (`pentagonCoefficient_X_swapColumns_X`).

The condition on the turn row cannot be dropped: when the turn row is the row of `X_b`, the
pentagon with initial side `a` is not counted, and the pentagons turning on their initial side that
are counted instead may carry an `O`-marking or end at another grid state. The data that
`ColumnCommutationData.ofNoninterleaving` attaches to every column commutation satisfies the
condition, so its commutation map always sends `x⁻(G)` to `x⁻(G')`
(`commutationMap_ofNoninterleaving_single_X`).

## Main results

* `TauCeti.GridDiagram.pentagonCoefficient_X_swapColumns_X`: if the turn row is not the row of
  `X_b`, the pentagon map has coefficient `1` from `G.X` to `G'.X`.
* `TauCeti.GridDiagram.commutationMap_single_X`: if the turn row is not the row of `X_b`, the
  commutation map sends the `X`-marking state of `G` to that of the commuted diagram.
* `TauCeti.GridDiagram.unblockedHomologyCommutationMap_XMarkingClass`: under the same condition,
  the induced map on `GH⁻` sends the class of the `X`-marking state to the class of the
  `X`-marking state.
* `TauCeti.GridDiagram.commutationMap_ofNoninterleaving_single_X`: the commutation map of the data
  attached to every column commutation sends the `X`-marking state of `G` to that of the commuted
  diagram.

## References

* P. Ozsváth, Z. Szabó, D. Thurston, *Legendrian knots, transverse knots and combinatorial Floer
  homology*, Geom. Topol. 12 (2008), arXiv:math/0611841: the grid states `x⁺` and `x⁻`, their
  classes `λ⁺` and `λ⁻`, and their invariance under commutation.
* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Chapter 12: the same material in the conventions of the grid book.
-/

public section

namespace TauCeti

open MvPolynomial

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-! ### The counted pentagons leaving the `X`-marking state -/

/-- If the turn row is not the row of the `X`-marking of the column after the replaced line, no
counted pentagon turning on its initial side leaves the `X`-marking state: such a pentagon starts
at the lower-left corner of that marking's square and covers it. -/
theorem initialPentagons_X_eq_empty (C : ColumnTurn n)
    (hs : C.turnRow ≠ G.X (finRotate n C.column)) (y : GridState n) :
    G.initialPentagons C G.X y = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun P hP => ?_
  have hX := ((P.disjoint_coveredSquares_XSet_iff G).mp ((G.mem_initialPentagons P).mp hP).2).2.2
  rw [GridRectangleBetween.bottom_def, P.left_eq] at hX
  exact hX (Grid.left_mem_cIco (Ne.symm hs))

/-- Every counted pentagon turning on its terminal side that leaves the `X`-marking state has
initial side the first commuted column: an initial side `j` elsewhere starts at the lower-left
corner of the square of the `X`-marking of column `j` and covers it. -/
private theorem left_eq_of_mem_pentagons_X {C : ColumnTurn n} {y : GridState n}
    {P : GridPentagonBetween C.column C.turnRow G.X y} (hP : P ∈ G.pentagons C G.X y) :
    P.left = C.column := by
  by_contra hj
  have hX := ((P.disjoint_coveredSquares_XSet_iff G).mp ((G.mem_pentagons P).mp hP).2).1
  refine hX P.left hj (Grid.left_mem_cIco P.left_ne) ?_
  rw [GridRectangleBetween.bottom_def, GridRectangleBetween.top_def, P.right_eq]
  exact Grid.left_mem_cIco fun h => P.left_ne (G.X.toPerm.injective h)

/-- No counted pentagon turning on its terminal side leaves the `X`-marking state for a grid state
other than the `X`-marking state of the commuted diagram. -/
theorem pentagons_X_eq_empty (C : ColumnTurn n) {y : GridState n}
    (hy : y ≠ (G.swapColumns C.column (finRotate n C.column)).X) :
    G.pentagons C G.X y = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun P hP => hy ?_
  rw [P.target_eq_swapColumns, G.left_eq_of_mem_pentagons_X hP, swapColumns_X]

/-! ### The commutation map on the `X`-marking state -/

section Chain

variable (R : Type*) [CommSemiring R]

/-- For validated column-commutation data whose turn row is not the row of the `X`-marking of the
second commuted column, the pentagon map has coefficient `1` from the `X`-marking state of `G` to
that of the commuted diagram: the one counted pentagon is one column wide and carries no
`O`-marking. -/
theorem pentagonCoefficient_X_swapColumns_X (C : ColumnCommutationData G)
    (hs : C.turnRow ≠ G.X (finRotate n C.column)) :
    G.pentagonCoefficient R C G.X (G.swapColumns C.column (finRotate n C.column)).X = 1 := by
  set a := C.column
  set b := finRotate n a
  have hab : a ≠ b := C.column_ne_next
  have hXab : G.X a ≠ G.X b := fun h => hab (G.X.toPerm.injective h)
  let P : GridPentagonBetween a C.turnRow G.X (G.X.swapColumns a b) :=
    .ofSwapColumns G.X a hab
      (Grid.mem_cIco_of_mem_insert_cIco C.X_column_below C.X_next_above hXab hs)
  have hPleft : P.left = a := GridPentagonBetween.ofSwapColumns_left _ _ _ _
  have hPbottom : P.bottom = G.X a := by rw [GridRectangleBetween.bottom_def, hPleft]
  have hPtop : P.top = G.X b := by rw [GridRectangleBetween.top_def, P.right_eq]
  -- `P` is one column wide, so away from columns `a` and `b` it covers nothing.
  have hcols (c : Fin n) (hca : c ≠ a) : c ∉ Grid.cIco P.left b := by
    rw [hPleft, Grid.cIco_eq_singleton_iff.mpr ⟨rfl, rfl, hab⟩, Finset.mem_singleton]
    exact hca
  have hPmem : P ∈ G.pentagons C G.X (G.X.swapColumns a b) := by
    refine (G.mem_pentagons P).mpr
      ⟨P.isEmpty_of_right_eq_finRotate (by rw [P.right_eq, hPleft]), ?_⟩
    refine (P.disjoint_coveredSquares_XSet_iff G).mpr
      ⟨fun c hca hc => (hcols c hca hc).elim, ?_, ?_⟩
    · rw [hPtop]
      exact Grid.notMem_cIoo_of_mem_insert_cIco C.X_column_below C.X_next_above
    · rw [hPbottom]
      exact Grid.notMem_cIco_of_mem_insert_cIco C.X_column_below C.X_next_above hXab
  have hO : G.pentagonOColumns C P = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun c hc => ?_
    rw [mem_pentagonOColumns, P.mem_coveredSquares] at hc
    rcases hc with ⟨hca, hc, -⟩ | ⟨rfl, hO⟩ | ⟨rfl, hO⟩
    · exact hcols _ hca hc
    · rw [hPtop] at hO
      exact Grid.notMem_cIoo_of_mem_insert_cIco C.O_column_below C.X_next_above hO
    · rw [hPbottom] at hO
      exact Grid.notMem_cIco_of_noninterleaving C.O_column_below C.X_column_below C.O_next_above
        C.X_next_above C.noninterleaving (G.disjoint a) (G.disjoint b) hs hO
  rw [pentagonCoefficient_def, swapColumns_X,
    Finset.eq_singleton_iff_unique_mem.mpr ⟨hPmem, fun Q _ => Subsingleton.elim Q P⟩,
    Finset.sum_singleton, pentagonWeight_eq_monomial, hO, Finset.sum_empty, monomial_zero', C_1]

/-- **The commutation map preserves the `X`-marking state.** For validated column-commutation
data whose turn row is not the row of the `X`-marking of the second commuted column, the
commutation map sends the `X`-marking state of `G` to the `X`-marking state of the commuted
diagram. -/
theorem commutationMap_single_X (C : ColumnCommutationData G)
    (hs : C.turnRow ≠ G.X (finRotate n C.column)) :
    G.commutationMap R C (Finsupp.single G.X 1) =
      Finsupp.single (G.swapColumns C.column (finRotate n C.column)).X 1 := by
  refine Finsupp.ext fun y => ?_
  rw [commutationMap_single_apply, commutationPentagonCoefficient_def,
    initialPentagonCoefficient_def, G.initialPentagons_X_eq_empty C hs, Finset.sum_empty, add_zero]
  by_cases hy : y = (G.swapColumns C.column (finRotate n C.column)).X
  · rw [hy, G.pentagonCoefficient_X_swapColumns_X R C hs, Finsupp.single_eq_same]
  · rw [pentagonCoefficient_def, G.pentagons_X_eq_empty C hy, Finset.sum_empty,
      Finsupp.single_eq_of_ne hy]

/-- The commutation map of the data attached to a column commutation sends the `X`-marking state
of `G` to the `X`-marking state of the commuted diagram. -/
theorem commutationMap_ofNoninterleaving_single_X {a : Fin n} (ha : a ≠ finRotate n a)
    (hG : G.ColumnsNoninterleaving a (finRotate n a)) :
    G.commutationMap R (ColumnCommutationData.ofNoninterleaving a ha hG) (Finsupp.single G.X 1) =
      Finsupp.single (G.swapColumns a (finRotate n a)).X 1 := by
  have h := G.commutationMap_single_X R (ColumnCommutationData.ofNoninterleaving a ha hG)
  simp only [ColumnCommutationData.ofNoninterleaving_column] at h
  exact h (ColumnCommutationData.ofNoninterleaving_turnRow_ne ha hG)

end Chain

/-! ### The class of the `X`-marking state in `GH⁻` -/

section Homology

variable (R : Type*) [CommRing R] [CharP R 2]

/-- **The commutation map on `GH⁻` preserves the class of the `X`-marking state.** Under the
condition of `commutationMap_single_X`, the induced map on unblocked grid homology sends the
class of the `X`-marking state of `G` to that of the commuted diagram. -/
theorem unblockedHomologyCommutationMap_XMarkingClass (C : ColumnCommutationData G)
    (hs : C.turnRow ≠ G.X (finRotate n C.column)) :
    G.unblockedHomologyCommutationMap R C (G.XMarkingClass R) =
      (G.swapColumns C.column (finRotate n C.column)).XMarkingClass R := by
  rw [XMarkingClass_def, unblockedHomologyCommutationMap_unblockedHomologyClass, XMarkingClass_def]
  congr 1
  refine Subtype.ext ?_
  simp only [coe_XMarkingCycle, G.commutationMap_single_X R C hs]

end Homology

end GridDiagram

end TauCeti
