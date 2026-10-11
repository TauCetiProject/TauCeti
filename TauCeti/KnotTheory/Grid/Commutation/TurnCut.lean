/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Decomposition
public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Decomposition

/-!
# Composite domains cut at the turn point

Let `b = finRotate n a` be the grid line replaced in a column commutation, and `s` the turn row.
A pentagon turning on its terminal side ends on `b`, and one turning on its initial side starts
on `b`. Consider two oriented rectangles, the first ending on `b` and the second starting on it,
both spanning the turn row. Their union is cut at the turn point by the line `β` on one side
and by the curve `γ` on the other, and it decomposes in two ways in the chain-map equation of the
commutation map: as a rectangle of the original diagram followed by an initial-side pentagon, or
as a terminal-side pentagon followed by a rectangle of the commuted diagram. The same holds in the
other order, for a first rectangle starting on `b` and a second one ending on `b`: a rectangle
followed by a terminal-side pentagon, or an initial-side pentagon followed by a rectangle of the
commuted diagram.

No recut is involved: the two decompositions have the same underlying rectangles, and only the
reading of the turn point changes. In the first order the two rectangles share their bottom row,
and the readings differ only in column `a`: one covers the rows of the first rectangle and the
rows of the second above the turn row, the other the rows of the second rectangle and the rows of
the first above the turn row, and both make up the same multiset of rows. In the second order the
two rectangles share their top row, and the readings differ only in column `b`, where the rows
below the turn row play the same part. So the two composite domains cover the same squares with
the same multiplicities, once the rectangle of the commuted diagram is read with its two commuted
columns exchanged
(`GridPentagonBetween.coveredSquares_val_add_val_turnCut` and
`GridInitialPentagonBetween.coveredSquares_val_add_val_turnCut`). Hence a counted decomposition
read the other way is counted and has the same monomial weight over any commutative semiring.
Thus in each order the two readings have equal total weight; when addition is cancellative, these
matched totals can be removed from the two sides of the chain-map equation (`GridDiagram.
sum_rectanglePentagonWeight_add_sum_rectangleInitialPentagonWeight_eq_iff_sdiff_turnCuts`).

## Main definitions

* `TauCeti.GridRectangleInitialPentagonDecomposition.toPentagonRectangle` and
  `TauCeti.GridPentagonRectangleDecomposition.toRectangleInitialPentagon`: the two mutually
  inverse readings in the first order.
* `TauCeti.GridRectanglePentagonDecomposition.toInitialPentagonRectangle` and
  `TauCeti.GridInitialPentagonRectangleDecomposition.toRectanglePentagon`: the two mutually
  inverse readings in the second order.
* `TauCeti.GridDiagram.rectangleInitialPentagonTurnCuts`,
  `TauCeti.GridDiagram.pentagonRectangleTurnCuts`, `TauCeti.GridDiagram.rectanglePentagonTurnCuts`
  and `TauCeti.GridDiagram.initialPentagonRectangleTurnCuts`: the counted decompositions of each
  kind that admit the other reading.

## Main results

* `TauCeti.GridDiagram.
  pentagonRectangleWeight_eq_rectangleInitialPentagonWeight_of_val_add_val_eq` and
  `TauCeti.GridDiagram.
  initialPentagonRectangleWeight_eq_rectanglePentagonWeight_of_val_add_val_eq`:
  composite domains of the two kinds of pentagon covering the same squares have the same weight.
* `TauCeti.GridDiagram.toPentagonRectangle_mem_pentagonRectangleDecompositions` and its three
  siblings, and `TauCeti.GridDiagram.pentagonRectangleWeight_toPentagonRectangle` and its three
  siblings: a counted decomposition read the other way is counted, with the same weight.
* `TauCeti.GridDiagram.
  sum_rectangleInitialPentagonWeight_turnCuts_eq_sum_pentagonRectangleWeight` and
  `TauCeti.GridDiagram.
  sum_rectanglePentagonWeight_turnCuts_eq_sum_initialPentagonRectangleWeight`:
  the two readings identify the total weights of the families.
* `TauCeti.GridDiagram.
  sum_rectanglePentagonWeight_add_sum_rectangleInitialPentagonWeight_eq_iff_sdiff_turnCuts`:
  all four families can be removed from the chain-map equation.

## References

These are the domains of the chain-map equation with a corner at the turn point, which
Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559), decompose by cutting along `β` or along `γ`.
-/

public section

namespace TauCeti

variable {n : ℕ} {a s : Fin n}

namespace GridPentagonBetween

/-- A pentagon turning on its terminal side followed by one turning on its initial side covers,
read as a pentagon followed by a rectangle of the commuted diagram, the same squares with the same
multiplicities as read as a rectangle followed by an initial-side pentagon. The squares of the
rectangle of the commuted diagram are read with the two commuted columns exchanged. -/
theorem coveredSquares_val_add_val_turnCut {x y z : GridState n}
    (P : GridPentagonBetween a s x y) (Q : GridInitialPentagonBetween a s y z) :
    P.coveredSquares.val +
        (Q.toGridRectangle.coveredSquares.map
          ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding).val =
      P.toGridRectangle.coveredSquares.val + Q.coveredSquares.val := by
  -- The two pentagons share their bottom row, the row of `x` on the initial side of `P`.
  have hbottom : Q.bottom = P.bottom := by
    rw [GridRectangleBetween.bottom_def, Q.left_eq, ← P.right_eq, P.map_right,
      GridRectangleBetween.bottom_def]
  have hP := Grid.ite_mem_cIco_eq_add_add P.turn_mem_cIco_bottom_top
  have hQ := Grid.ite_mem_cIco_eq_add_add Q.turn_mem_cIco_bottom_top
  rw [hbottom] at hQ
  have hab := P.ne_finRotate
  refine Multiset.ext.mpr fun p => ?_
  simp only [Multiset.count_add, Multiset.count_eq_of_nodup (Finset.nodup _), Finset.mem_val,
    Finset.mem_map_equiv, Equiv.prodCongr_symm, Equiv.symm_swap, Equiv.refl_symm,
    Equiv.prodCongr_apply]
  obtain ⟨c, t⟩ := p
  simp only [Prod.map_apply, Equiv.refl_apply, GridRectangle.mem_coveredSquares,
    GridRectangle.mem_coveredColumns, GridRectangle.mem_coveredRows,
    GridRectangleBetween.toGridRectangle_left, GridRectangleBetween.toGridRectangle_right,
    GridRectangleBetween.toGridRectangle_bottom, GridRectangleBetween.toGridRectangle_top,
    P.right_eq, Q.left_eq, hbottom]
  by_cases hca : c = a
  · subst hca
    -- In column `a`, both sides cover the rows of `P` and of `Q` above the turn row, and the
    -- rows from the common bottom row up to the turn row once.
    simp only [Equiv.swap_apply_left, P.mem_coveredSquares, Q.mk_mem_coveredSquares_left_column,
      Grid.self_mem_cIco_finRotate P.left_ne, Grid.left_mem_cIco (Q.left_eq ▸ Q.left_ne_right),
      hab, true_and, ne_eq, not_true_eq_false, false_and, false_or, or_false]
    have := hP t
    have := hQ t
    omega
  by_cases hcb : c = finRotate n a
  · subst hcb
    have h2 : a ∉ Grid.cIco (finRotate n a) Q.right := by simp
    simp only [Equiv.swap_apply_right, P.mem_coveredSquares, Q.mk_mem_coveredSquares_right_column,
      Grid.right_notMem_cIco P.left (finRotate n a), h2, hab.symm, hbottom, ne_eq, false_and,
      false_or, and_false, not_false_eq_true, true_and, ↓reduceIte, add_zero, zero_add]
  · simp only [Equiv.swap_apply_of_ne_of_ne hca hcb,
      P.mem_coveredSquares_iff_of_ne (p := (c, t)) hca hcb,
      Q.mem_coveredSquares_iff_of_ne (p := (c, t)) hca hcb, GridRectangle.mem_coveredSquares,
      GridRectangle.mem_coveredColumns, GridRectangle.mem_coveredRows,
      GridRectangleBetween.toGridRectangle_left, GridRectangleBetween.toGridRectangle_right,
      GridRectangleBetween.toGridRectangle_bottom, GridRectangleBetween.toGridRectangle_top,
      P.right_eq, Q.left_eq, hbottom]

end GridPentagonBetween

namespace GridInitialPentagonBetween

/-- A pentagon turning on its initial side followed by one turning on its terminal side covers,
read as an initial-side pentagon followed by a rectangle of the commuted diagram, the same
squares with the same multiplicities as read as a rectangle followed by a pentagon. The squares
of the rectangle of the commuted diagram are read with the two commuted columns exchanged. -/
theorem coveredSquares_val_add_val_turnCut {x y z : GridState n}
    (Q : GridInitialPentagonBetween a s x y) (P : GridPentagonBetween a s y z) :
    Q.coveredSquares.val +
        (P.toGridRectangle.coveredSquares.map
          ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding).val =
      Q.toGridRectangle.coveredSquares.val + P.coveredSquares.val := by
  -- The two pentagons share their top row, the row of `x` on the terminal side of `Q`.
  have htop : P.top = Q.top := by
    rw [GridRectangleBetween.top_def, P.right_eq, ← Q.left_eq, Q.map_left,
      GridRectangleBetween.top_def]
  have hP := Grid.ite_mem_cIco_eq_add_add P.turn_mem_cIco_bottom_top
  have hQ := Grid.ite_mem_cIco_eq_add_add Q.turn_mem_cIco_bottom_top
  rw [htop] at hP
  have hab := P.ne_finRotate
  refine Multiset.ext.mpr fun p => ?_
  simp only [Multiset.count_add, Multiset.count_eq_of_nodup (Finset.nodup _), Finset.mem_val,
    Finset.mem_map_equiv, Equiv.prodCongr_symm, Equiv.symm_swap, Equiv.refl_symm,
    Equiv.prodCongr_apply]
  obtain ⟨c, t⟩ := p
  simp only [Prod.map_apply, Equiv.refl_apply, GridRectangle.mem_coveredSquares,
    GridRectangle.mem_coveredColumns, GridRectangle.mem_coveredRows,
    GridRectangleBetween.toGridRectangle_left, GridRectangleBetween.toGridRectangle_right,
    GridRectangleBetween.toGridRectangle_bottom, GridRectangleBetween.toGridRectangle_top,
    P.right_eq, Q.left_eq, htop]
  by_cases hca : c = a
  · subst hca
    have h2 : c ∉ Grid.cIco (finRotate n c) Q.right := by simp
    simp only [Equiv.swap_apply_left, P.mem_coveredSquares, Q.mk_mem_coveredSquares_left_column,
      Grid.right_notMem_cIco P.left (finRotate n c), h2, hab, htop, ne_eq, false_and, false_or,
      true_and, ↓reduceIte, add_zero, zero_add, or_false, not_true_eq_false]
  by_cases hcb : c = finRotate n a
  · subst hcb
    -- In column `finRotate n a`, both sides cover the rows of `Q` and of `P` below the turn row,
    -- and the rows from the turn row up to the common top row once.
    simp only [Equiv.swap_apply_right, P.mem_coveredSquares, Q.mk_mem_coveredSquares_right_column,
      Grid.self_mem_cIco_finRotate P.left_ne, Grid.right_notMem_cIco P.left (finRotate n a),
      Grid.left_mem_cIco (Q.left_eq ▸ Q.left_ne_right), hab.symm, htop, true_and, ne_eq,
      false_and, false_or, not_false_eq_true, and_false]
    have := hP t
    have := hQ t
    omega
  · simp only [Equiv.swap_apply_of_ne_of_ne hca hcb,
      P.mem_coveredSquares_iff_of_ne (p := (c, t)) hca hcb,
      Q.mem_coveredSquares_iff_of_ne (p := (c, t)) hca hcb, GridRectangle.mem_coveredSquares,
      GridRectangle.mem_coveredColumns, GridRectangle.mem_coveredRows,
      GridRectangleBetween.toGridRectangle_left, GridRectangleBetween.toGridRectangle_right,
      GridRectangleBetween.toGridRectangle_bottom, GridRectangleBetween.toGridRectangle_top,
      P.right_eq, Q.left_eq, htop]

end GridInitialPentagonBetween

/-! ### Rectangles ending on the replaced line followed by rectangles starting there -/

namespace GridRectangleInitialPentagonDecomposition

variable {x z : GridState n}

/-- Read a rectangle ending on the replaced line and spanning the turn row, followed by an
initial-side pentagon, as a terminal-side pentagon followed by a rectangle. -/
def toPentagonRectangle (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hright : D.first.right = finRotate n a) (hturn : s ∈ Grid.cIco D.first.bottom D.first.top) :
    GridPentagonRectangleDecomposition a s x z where
  middle := D.middle
  pentagon := GridPentagonBetween.ofRightEq D.first hright hturn
  rectangle := D.second

/-- Reading the turn point the other way keeps the underlying rectangles. -/
@[simp]
theorem toPentagonRectangle_toRectangleDecomposition
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hright : D.first.right = finRotate n a) (hturn : s ∈ Grid.cIco D.first.bottom D.first.top) :
    (D.toPentagonRectangle hright hturn).toRectangleDecomposition =
      D.toGridRectangleDecomposition := by
  ext <;> simp [toPentagonRectangle]

end GridRectangleInitialPentagonDecomposition

namespace GridPentagonRectangleDecomposition

variable {x z : GridState n}

/-- Read a pentagon followed by a rectangle starting on the replaced line and spanning the turn
row as a rectangle followed by an initial-side pentagon. -/
def toRectangleInitialPentagon (E : GridPentagonRectangleDecomposition a s x z)
    (hleft : E.rectangle.left = finRotate n a)
    (hturn : s ∈ Grid.cIco E.rectangle.bottom E.rectangle.top) :
    GridRectangleInitialPentagonDecomposition a s x z where
  middle := E.middle
  first := E.pentagon.toGridRectangleBetween
  second := E.rectangle
  second_left_eq := hleft
  second_turn_mem := hturn

/-- Reading the turn point the other way keeps the underlying rectangles. -/
@[simp]
theorem toRectangleInitialPentagon_toGridRectangleDecomposition
    (E : GridPentagonRectangleDecomposition a s x z) (hleft : E.rectangle.left = finRotate n a)
    (hturn : s ∈ Grid.cIco E.rectangle.bottom E.rectangle.top) :
    (E.toRectangleInitialPentagon hleft hturn).toGridRectangleDecomposition =
      E.toRectangleDecomposition := by
  ext <;> simp [toRectangleInitialPentagon]

/-- Reading the turn point the other way and back gives the original decomposition. -/
@[simp]
theorem toRectangleInitialPentagon_toPentagonRectangle
    (D : GridRectangleInitialPentagonDecomposition a s x z)
    (hright : D.first.right = finRotate n a) (hturn : s ∈ Grid.cIco D.first.bottom D.first.top)
    (hleft : (D.toPentagonRectangle hright hturn).rectangle.left = finRotate n a)
    (hturn' : s ∈ Grid.cIco (D.toPentagonRectangle hright hturn).rectangle.bottom
      (D.toPentagonRectangle hright hturn).rectangle.top) :
    (D.toPentagonRectangle hright hturn).toRectangleInitialPentagon hleft hturn' = D :=
  GridRectangleInitialPentagonDecomposition.ext (by simp)

/-- Reading the turn point the other way and back gives the original decomposition. -/
@[simp]
theorem toPentagonRectangle_toRectangleInitialPentagon
    (E : GridPentagonRectangleDecomposition a s x z) (hleft : E.rectangle.left = finRotate n a)
    (hturn : s ∈ Grid.cIco E.rectangle.bottom E.rectangle.top)
    (hright : (E.toRectangleInitialPentagon hleft hturn).first.right = finRotate n a)
    (hturn' : s ∈ Grid.cIco (E.toRectangleInitialPentagon hleft hturn).first.bottom
      (E.toRectangleInitialPentagon hleft hturn).first.top) :
    (E.toRectangleInitialPentagon hleft hturn).toPentagonRectangle hright hturn' = E :=
  toRectangleDecomposition_injective (by simp)

end GridPentagonRectangleDecomposition

/-! ### Rectangles starting on the replaced line followed by rectangles ending there -/

namespace GridRectanglePentagonDecomposition

variable {x z : GridState n}

/-- Read a rectangle starting on the replaced line and spanning the turn row, followed by a
pentagon, as an initial-side pentagon followed by a rectangle. -/
def toInitialPentagonRectangle (D : GridRectanglePentagonDecomposition a s x z)
    (hleft : D.rectangle.left = finRotate n a)
    (hturn : s ∈ Grid.cIco D.rectangle.bottom D.rectangle.top) :
    GridInitialPentagonRectangleDecomposition a s x z where
  middle := D.middle
  first := D.rectangle
  second := D.pentagon.toGridRectangleBetween
  first_left_eq := hleft
  first_turn_mem := hturn

/-- Reading the turn point the other way keeps the underlying rectangles. -/
@[simp]
theorem toInitialPentagonRectangle_toGridRectangleDecomposition
    (D : GridRectanglePentagonDecomposition a s x z) (hleft : D.rectangle.left = finRotate n a)
    (hturn : s ∈ Grid.cIco D.rectangle.bottom D.rectangle.top) :
    (D.toInitialPentagonRectangle hleft hturn).toGridRectangleDecomposition =
      D.toRectangleDecomposition := by
  ext <;> simp [toInitialPentagonRectangle]

end GridRectanglePentagonDecomposition

namespace GridInitialPentagonRectangleDecomposition

variable {x z : GridState n}

/-- Read an initial-side pentagon followed by a rectangle ending on the replaced line and
spanning the turn row as a rectangle followed by a terminal-side pentagon. -/
def toRectanglePentagon (E : GridInitialPentagonRectangleDecomposition a s x z)
    (hright : E.second.right = finRotate n a)
    (hturn : s ∈ Grid.cIco E.second.bottom E.second.top) :
    GridRectanglePentagonDecomposition a s x z where
  middle := E.middle
  rectangle := E.first
  pentagon := GridPentagonBetween.ofRightEq E.second hright hturn

/-- Reading the turn point the other way keeps the underlying rectangles. -/
@[simp]
theorem toRectanglePentagon_toRectangleDecomposition
    (E : GridInitialPentagonRectangleDecomposition a s x z)
    (hright : E.second.right = finRotate n a)
    (hturn : s ∈ Grid.cIco E.second.bottom E.second.top) :
    (E.toRectanglePentagon hright hturn).toRectangleDecomposition =
      E.toGridRectangleDecomposition := by
  ext <;> simp [toRectanglePentagon]

/-- Reading the turn point the other way and back gives the original decomposition. -/
@[simp]
theorem toInitialPentagonRectangle_toRectanglePentagon
    (E : GridInitialPentagonRectangleDecomposition a s x z)
    (hright : E.second.right = finRotate n a) (hturn : s ∈ Grid.cIco E.second.bottom E.second.top)
    (hleft : (E.toRectanglePentagon hright hturn).rectangle.left = finRotate n a)
    (hturn' : s ∈ Grid.cIco (E.toRectanglePentagon hright hturn).rectangle.bottom
      (E.toRectanglePentagon hright hturn).rectangle.top) :
    (E.toRectanglePentagon hright hturn).toInitialPentagonRectangle hleft hturn' = E :=
  ext (by simp)

/-- Reading the turn point the other way and back gives the original decomposition. -/
@[simp]
theorem toRectanglePentagon_toInitialPentagonRectangle
    (D : GridRectanglePentagonDecomposition a s x z) (hleft : D.rectangle.left = finRotate n a)
    (hturn : s ∈ Grid.cIco D.rectangle.bottom D.rectangle.top)
    (hright : (D.toInitialPentagonRectangle hleft hturn).second.right = finRotate n a)
    (hturn' : s ∈ Grid.cIco (D.toInitialPentagonRectangle hleft hturn).second.bottom
      (D.toInitialPentagonRectangle hleft hturn).second.top) :
    (D.toInitialPentagonRectangle hleft hturn).toRectanglePentagon hright hturn' = D :=
  GridRectanglePentagonDecomposition.toRectangleDecomposition_injective (by simp)

end GridInitialPentagonRectangleDecomposition

namespace GridDiagram

variable (G : GridDiagram n) (C : ColumnCommutationData G)

local notation "b" => finRotate n C.column

/-! ### Weights and countedness of the two readings -/

section Weights

variable (R : Type*) [CommSemiring R]

/-- A pentagon followed by a rectangle of the commuted diagram has the weight of a rectangle
followed by an initial-side pentagon when the two composite domains cover the same squares with
the same multiplicities, the squares of the rectangle of the commuted diagram being read in the
original diagram, that is with the two commuted columns exchanged. -/
theorem pentagonRectangleWeight_eq_rectangleInitialPentagonWeight_of_val_add_val_eq
    {x z : GridState n} (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z)
    (E : GridPentagonRectangleDecomposition C.column C.turnRow x z)
    (h : E.pentagon.coveredSquares.val +
        (E.rectangle.toGridRectangle.coveredSquares.map
          ((Equiv.swap C.column b).prodCongr (Equiv.refl (Fin n))).toEmbedding).val =
      D.first.toGridRectangle.coveredSquares.val + D.pentagon.coveredSquares.val) :
    G.pentagonRectangleWeight C R E = G.rectangleInitialPentagonWeight C R D := by
  rw [pentagonRectangleWeight_def, rectangleInitialPentagonWeight_def,
    pentagonWeight_eq_prod_coveredSquares, initialPentagonWeight_eq_prod_coveredSquares,
    OMonomial_swapColumns_eq_prod_swapSquareWeight, rename_OMonomial_eq_prod_swapSquareWeight]
  simp only [← swapSquareWeight_def, Finset.prod_eq_multiset_prod, ← Multiset.prod_add,
    ← Multiset.map_add, h]

/-- An initial-side pentagon followed by a rectangle of the commuted diagram has the weight of a
rectangle followed by a pentagon when the two composite domains cover the same squares with the
same multiplicities, the squares of the rectangle of the commuted diagram being read in the
original diagram, that is with the two commuted columns exchanged. -/
theorem initialPentagonRectangleWeight_eq_rectanglePentagonWeight_of_val_add_val_eq
    {x z : GridState n} (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (E : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z)
    (h : E.pentagon.coveredSquares.val +
        (E.second.toGridRectangle.coveredSquares.map
          ((Equiv.swap C.column b).prodCongr (Equiv.refl (Fin n))).toEmbedding).val =
      D.rectangle.toGridRectangle.coveredSquares.val + D.pentagon.coveredSquares.val) :
    G.initialPentagonRectangleWeight C R E = G.rectanglePentagonWeight C R D := by
  rw [initialPentagonRectangleWeight_def, rectanglePentagonWeight_def,
    initialPentagonWeight_eq_prod_coveredSquares, pentagonWeight_eq_prod_coveredSquares,
    OMonomial_swapColumns_eq_prod_swapSquareWeight, rename_OMonomial_eq_prod_swapSquareWeight]
  simp only [← swapSquareWeight_def, Finset.prod_eq_multiset_prod, ← Multiset.prod_add,
    ← Multiset.map_add, h]

end Weights

variable {x z : GridState n}

/-- A counted rectangle ending on the replaced line and spanning the turn row, followed by an
initial-side pentagon, read as a terminal-side pentagon followed by a rectangle of the commuted
diagram, is counted. -/
theorem toPentagonRectangle_mem_pentagonRectangleDecompositions
    {D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z}
    (hD : D ∈ G.rectangleInitialPentagonDecompositions C x z) (hright : D.first.right = b)
    (hturn : C.turnRow ∈ Grid.cIco D.first.bottom D.first.top) :
    D.toPentagonRectangle hright hturn ∈ G.pentagonRectangleDecompositions C x z := by
  rw [mem_rectangleInitialPentagonDecompositions, mem_unblockedRectangles,
    mem_initialPentagons] at hD
  have hunion := congrArg Multiset.toFinset
    ((GridPentagonBetween.ofRightEq D.first hright hturn).coveredSquares_val_add_val_turnCut
      D.pentagon)
  simp only [Multiset.toFinset_add, Finset.val_toFinset,
    GridPentagonBetween.ofRightEq_toGridRectangleBetween,
    GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween] at hunion
  have hX := Finset.disjoint_union_left.mp
    (hunion ▸ Finset.disjoint_union_left.mpr ⟨hD.1.2, hD.2.2⟩)
  rw [mem_pentagonRectangleDecompositions, mem_pentagons,
    (G.swapColumns C.column b).mem_unblockedRectangles, ← G.disjoint_map_swapColumns_XSet_iff]
  simp only [GridRectangleInitialPentagonDecomposition.toPentagonRectangle,
    GridPentagonBetween.ofRightEq_toGridRectangleBetween]
  refine ⟨⟨hD.1.1, hX.1⟩, ?_, hX.2⟩
  simpa only [GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween] using
    hD.2.1

/-- A counted pentagon followed by a rectangle of the commuted diagram starting on the replaced
line and spanning the turn row, read as a rectangle followed by an initial-side pentagon, is
counted. -/
theorem toRectangleInitialPentagon_mem_rectangleInitialPentagonDecompositions
    {E : GridPentagonRectangleDecomposition C.column C.turnRow x z}
    (hE : E ∈ G.pentagonRectangleDecompositions C x z) (hleft : E.rectangle.left = b)
    (hturn : C.turnRow ∈ Grid.cIco E.rectangle.bottom E.rectangle.top) :
    E.toRectangleInitialPentagon hleft hturn ∈
      G.rectangleInitialPentagonDecompositions C x z := by
  rw [mem_pentagonRectangleDecompositions, mem_pentagons,
    (G.swapColumns C.column b).mem_unblockedRectangles,
    ← G.disjoint_map_swapColumns_XSet_iff] at hE
  have hunion := congrArg Multiset.toFinset
    (E.pentagon.coveredSquares_val_add_val_turnCut
      (E.toRectangleInitialPentagon hleft hturn).pentagon)
  simp only [Multiset.toFinset_add, Finset.val_toFinset,
    GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween,
    GridPentagonRectangleDecomposition.toRectangleInitialPentagon] at hunion
  have hX := Finset.disjoint_union_left.mp
    (hunion ▸ Finset.disjoint_union_left.mpr ⟨hE.1.2, hE.2.2⟩)
  rw [mem_rectangleInitialPentagonDecompositions, mem_unblockedRectangles, mem_initialPentagons,
    GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween]
  simp only [GridPentagonRectangleDecomposition.toRectangleInitialPentagon]
  exact ⟨⟨hE.1.1, hX.1⟩, hE.2.1, hX.2⟩

/-- A counted rectangle starting on the replaced line and spanning the turn row, followed by a
pentagon, read as an initial-side pentagon followed by a rectangle of the commuted diagram, is
counted. -/
theorem toInitialPentagonRectangle_mem_initialPentagonRectangleDecompositions
    {D : GridRectanglePentagonDecomposition C.column C.turnRow x z}
    (hD : D ∈ G.rectanglePentagonDecompositions C x z) (hleft : D.rectangle.left = b)
    (hturn : C.turnRow ∈ Grid.cIco D.rectangle.bottom D.rectangle.top) :
    D.toInitialPentagonRectangle hleft hturn ∈
      G.initialPentagonRectangleDecompositions C x z := by
  rw [mem_rectanglePentagonDecompositions, mem_unblockedRectangles, mem_pentagons] at hD
  have hunion := congrArg Multiset.toFinset
    ((D.toInitialPentagonRectangle hleft hturn).pentagon.coveredSquares_val_add_val_turnCut
      D.pentagon)
  simp only [Multiset.toFinset_add, Finset.val_toFinset,
    GridInitialPentagonRectangleDecomposition.pentagon_toGridRectangleBetween,
    GridRectanglePentagonDecomposition.toInitialPentagonRectangle] at hunion
  have hX := Finset.disjoint_union_left.mp
    (hunion ▸ Finset.disjoint_union_left.mpr ⟨hD.1.2, hD.2.2⟩)
  rw [mem_initialPentagonRectangleDecompositions, mem_initialPentagons,
    (G.swapColumns C.column b).mem_unblockedRectangles, ← G.disjoint_map_swapColumns_XSet_iff,
    GridInitialPentagonRectangleDecomposition.pentagon_toGridRectangleBetween]
  exact ⟨⟨hD.1.1, hX.1⟩, hD.2.1, hX.2⟩

/-- A counted initial-side pentagon followed by a rectangle of the commuted diagram ending on the
replaced line and spanning the turn row, read as a rectangle followed by a pentagon, is
counted. -/
theorem toRectanglePentagon_mem_rectanglePentagonDecompositions
    {E : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z}
    (hE : E ∈ G.initialPentagonRectangleDecompositions C x z) (hright : E.second.right = b)
    (hturn : C.turnRow ∈ Grid.cIco E.second.bottom E.second.top) :
    E.toRectanglePentagon hright hturn ∈ G.rectanglePentagonDecompositions C x z := by
  rw [mem_initialPentagonRectangleDecompositions, mem_initialPentagons,
    (G.swapColumns C.column b).mem_unblockedRectangles,
    ← G.disjoint_map_swapColumns_XSet_iff,
    GridInitialPentagonRectangleDecomposition.pentagon_toGridRectangleBetween] at hE
  have hunion := congrArg Multiset.toFinset
    (E.pentagon.coveredSquares_val_add_val_turnCut (E.toRectanglePentagon hright hturn).pentagon)
  simp only [Multiset.toFinset_add, Finset.val_toFinset,
    GridInitialPentagonRectangleDecomposition.toRectanglePentagon,
    GridInitialPentagonRectangleDecomposition.pentagon_toGridRectangleBetween,
    GridPentagonBetween.ofRightEq_toGridRectangleBetween] at hunion
  have hX := Finset.disjoint_union_left.mp
    (hunion ▸ Finset.disjoint_union_left.mpr ⟨hE.1.2, hE.2.2⟩)
  rw [mem_rectanglePentagonDecompositions, mem_unblockedRectangles, mem_pentagons]
  simp only [GridInitialPentagonRectangleDecomposition.toRectanglePentagon,
    GridPentagonBetween.ofRightEq_toGridRectangleBetween]
  exact ⟨⟨hE.1.1, hX.1⟩, hE.2.1, hX.2⟩

section Weights

variable (R : Type*) [CommSemiring R]

/-- Reading a rectangle followed by an initial-side pentagon as a pentagon followed by a
rectangle preserves the weight. -/
theorem pentagonRectangleWeight_toPentagonRectangle
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z)
    (hright : D.first.right = b) (hturn : C.turnRow ∈ Grid.cIco D.first.bottom D.first.top) :
    G.pentagonRectangleWeight C R (D.toPentagonRectangle hright hturn) =
      G.rectangleInitialPentagonWeight C R D := by
  apply pentagonRectangleWeight_eq_rectangleInitialPentagonWeight_of_val_add_val_eq
  simpa only [GridRectangleInitialPentagonDecomposition.toPentagonRectangle,
    GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween,
    GridPentagonBetween.ofRightEq_toGridRectangleBetween] using
    (GridPentagonBetween.ofRightEq D.first hright hturn).coveredSquares_val_add_val_turnCut
      D.pentagon

/-- Reading a rectangle followed by a pentagon as an initial-side pentagon followed by a
rectangle preserves the weight. -/
theorem initialPentagonRectangleWeight_toInitialPentagonRectangle
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (hleft : D.rectangle.left = b)
    (hturn : C.turnRow ∈ Grid.cIco D.rectangle.bottom D.rectangle.top) :
    G.initialPentagonRectangleWeight C R (D.toInitialPentagonRectangle hleft hturn) =
      G.rectanglePentagonWeight C R D := by
  apply initialPentagonRectangleWeight_eq_rectanglePentagonWeight_of_val_add_val_eq
  simpa only [GridRectanglePentagonDecomposition.toInitialPentagonRectangle,
    GridInitialPentagonRectangleDecomposition.pentagon_toGridRectangleBetween] using
    (D.toInitialPentagonRectangle hleft hturn).pentagon.coveredSquares_val_add_val_turnCut
      D.pentagon

/-- Reading a pentagon followed by a rectangle as a rectangle followed by an initial-side
pentagon preserves the weight. -/
theorem rectangleInitialPentagonWeight_toRectangleInitialPentagon
    (E : GridPentagonRectangleDecomposition C.column C.turnRow x z)
    (hleft : E.rectangle.left = b)
    (hturn : C.turnRow ∈ Grid.cIco E.rectangle.bottom E.rectangle.top) :
    G.rectangleInitialPentagonWeight C R (E.toRectangleInitialPentagon hleft hturn) =
      G.pentagonRectangleWeight C R E := by
  refine (G.pentagonRectangleWeight_eq_rectangleInitialPentagonWeight_of_val_add_val_eq C R _ _
    ?_).symm
  simpa only [GridPentagonRectangleDecomposition.toRectangleInitialPentagon,
    GridRectangleInitialPentagonDecomposition.pentagon_toGridRectangleBetween] using
    E.pentagon.coveredSquares_val_add_val_turnCut
      (E.toRectangleInitialPentagon hleft hturn).pentagon

/-- Reading an initial-side pentagon followed by a rectangle as a rectangle followed by a
pentagon preserves the weight. -/
theorem rectanglePentagonWeight_toRectanglePentagon
    (E : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z)
    (hright : E.second.right = b) (hturn : C.turnRow ∈ Grid.cIco E.second.bottom E.second.top) :
    G.rectanglePentagonWeight C R (E.toRectanglePentagon hright hturn) =
      G.initialPentagonRectangleWeight C R E := by
  refine (G.initialPentagonRectangleWeight_eq_rectanglePentagonWeight_of_val_add_val_eq C R _ _
    ?_).symm
  simpa only [GridInitialPentagonRectangleDecomposition.toRectanglePentagon,
    GridInitialPentagonRectangleDecomposition.pentagon_toGridRectangleBetween,
    GridPentagonBetween.ofRightEq_toGridRectangleBetween] using
    E.pentagon.coveredSquares_val_add_val_turnCut (E.toRectanglePentagon hright hturn).pentagon

end Weights

/-! ### The four families and their cancellation -/

variable (x z) in
/-- The counted rectangle--initial-side pentagon decompositions whose rectangle ends on the
replaced line and spans the turn row. -/
noncomputable def rectangleInitialPentagonTurnCuts :
    Finset (GridRectangleInitialPentagonDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.rectangleInitialPentagonDecompositions C x z).filter fun D =>
    D.first.right = b ∧ C.turnRow ∈ Grid.cIco D.first.bottom D.first.top

/-- Membership in `GridDiagram.rectangleInitialPentagonTurnCuts`. -/
@[simp]
theorem mem_rectangleInitialPentagonTurnCuts
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z) :
    D ∈ G.rectangleInitialPentagonTurnCuts C x z ↔
      D ∈ G.rectangleInitialPentagonDecompositions C x z ∧ D.first.right = b ∧
        C.turnRow ∈ Grid.cIco D.first.bottom D.first.top := by
  classical
  simp [rectangleInitialPentagonTurnCuts]

variable (x z) in
/-- The counted pentagon--rectangle decompositions whose rectangle starts on the replaced line and
spans the turn row. -/
noncomputable def pentagonRectangleTurnCuts :
    Finset (GridPentagonRectangleDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.pentagonRectangleDecompositions C x z).filter fun E =>
    E.rectangle.left = b ∧ C.turnRow ∈ Grid.cIco E.rectangle.bottom E.rectangle.top

/-- Membership in `GridDiagram.pentagonRectangleTurnCuts`. -/
@[simp]
theorem mem_pentagonRectangleTurnCuts
    (E : GridPentagonRectangleDecomposition C.column C.turnRow x z) :
    E ∈ G.pentagonRectangleTurnCuts C x z ↔
      E ∈ G.pentagonRectangleDecompositions C x z ∧ E.rectangle.left = b ∧
        C.turnRow ∈ Grid.cIco E.rectangle.bottom E.rectangle.top := by
  classical
  simp [pentagonRectangleTurnCuts]

variable (x z) in
/-- The counted rectangle--pentagon decompositions whose rectangle starts on the replaced line and
spans the turn row. -/
noncomputable def rectanglePentagonTurnCuts :
    Finset (GridRectanglePentagonDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.rectanglePentagonDecompositions C x z).filter fun D =>
    D.rectangle.left = b ∧ C.turnRow ∈ Grid.cIco D.rectangle.bottom D.rectangle.top

/-- Membership in `GridDiagram.rectanglePentagonTurnCuts`. -/
@[simp]
theorem mem_rectanglePentagonTurnCuts
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z) :
    D ∈ G.rectanglePentagonTurnCuts C x z ↔
      D ∈ G.rectanglePentagonDecompositions C x z ∧ D.rectangle.left = b ∧
        C.turnRow ∈ Grid.cIco D.rectangle.bottom D.rectangle.top := by
  classical
  simp [rectanglePentagonTurnCuts]

variable (x z) in
/-- The counted initial-side pentagon--rectangle decompositions whose rectangle ends on the
replaced line and spans the turn row. -/
noncomputable def initialPentagonRectangleTurnCuts :
    Finset (GridInitialPentagonRectangleDecomposition C.column C.turnRow x z) := by
  classical
  exact (G.initialPentagonRectangleDecompositions C x z).filter fun E =>
    E.second.right = b ∧ C.turnRow ∈ Grid.cIco E.second.bottom E.second.top

/-- Membership in `GridDiagram.initialPentagonRectangleTurnCuts`. -/
@[simp]
theorem mem_initialPentagonRectangleTurnCuts
    (E : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z) :
    E ∈ G.initialPentagonRectangleTurnCuts C x z ↔
      E ∈ G.initialPentagonRectangleDecompositions C x z ∧ E.second.right = b ∧
        C.turnRow ∈ Grid.cIco E.second.bottom E.second.top := by
  classical
  simp [initialPentagonRectangleTurnCuts]

variable (R : Type*) [CommSemiring R]

variable (x z) in
/-- Reading the turn point the other way identifies the total weight of the rectangle--initial-side
pentagon decompositions cut at the turn point with that of the pentagon--rectangle ones. -/
theorem sum_rectangleInitialPentagonWeight_turnCuts_eq_sum_pentagonRectangleWeight :
    ∑ D ∈ G.rectangleInitialPentagonTurnCuts C x z, G.rectangleInitialPentagonWeight C R D =
      ∑ E ∈ G.pentagonRectangleTurnCuts C x z, G.pentagonRectangleWeight C R E := by
  refine Finset.sum_bij'
    (fun D hD => D.toPentagonRectangle ((G.mem_rectangleInitialPentagonTurnCuts C D).1 hD).2.1
      ((G.mem_rectangleInitialPentagonTurnCuts C D).1 hD).2.2)
    (fun E hE => E.toRectangleInitialPentagon ((G.mem_pentagonRectangleTurnCuts C E).1 hE).2.1
      ((G.mem_pentagonRectangleTurnCuts C E).1 hE).2.2) (fun D hD => ?_) (fun E hE => ?_)
    (fun D hD => by simp) (fun E hE => by simp)
    (fun D hD => (G.pentagonRectangleWeight_toPentagonRectangle C R D _ _).symm)
  · obtain ⟨hD, hright, hturn⟩ := (G.mem_rectangleInitialPentagonTurnCuts C D).1 hD
    refine (G.mem_pentagonRectangleTurnCuts C _).2
      ⟨G.toPentagonRectangle_mem_pentagonRectangleDecompositions C hD hright hturn, ?_⟩
    simpa only [GridRectangleInitialPentagonDecomposition.toPentagonRectangle] using
      ⟨D.second_left_eq, D.second_turn_mem⟩
  · obtain ⟨hE, hleft, hturn⟩ := (G.mem_pentagonRectangleTurnCuts C E).1 hE
    refine (G.mem_rectangleInitialPentagonTurnCuts C _).2
      ⟨G.toRectangleInitialPentagon_mem_rectangleInitialPentagonDecompositions C hE hleft hturn,
        ?_⟩
    simpa only [GridPentagonRectangleDecomposition.toRectangleInitialPentagon] using
      ⟨E.pentagon.right_eq, E.pentagon.turn_mem_cIco_bottom_top⟩

variable (x z) in
/-- Reading the turn point the other way identifies the total weight of the rectangle--pentagon
decompositions cut at the turn point with that of the initial-side pentagon--rectangle ones. -/
theorem sum_rectanglePentagonWeight_turnCuts_eq_sum_initialPentagonRectangleWeight :
    ∑ D ∈ G.rectanglePentagonTurnCuts C x z, G.rectanglePentagonWeight C R D =
      ∑ E ∈ G.initialPentagonRectangleTurnCuts C x z,
        G.initialPentagonRectangleWeight C R E := by
  refine Finset.sum_bij'
    (fun D hD => D.toInitialPentagonRectangle ((G.mem_rectanglePentagonTurnCuts C D).1 hD).2.1
      ((G.mem_rectanglePentagonTurnCuts C D).1 hD).2.2)
    (fun E hE => E.toRectanglePentagon ((G.mem_initialPentagonRectangleTurnCuts C E).1 hE).2.1
      ((G.mem_initialPentagonRectangleTurnCuts C E).1 hE).2.2) (fun D hD => ?_) (fun E hE => ?_)
    (fun D hD => by simp) (fun E hE => by simp)
    (fun D hD => (G.initialPentagonRectangleWeight_toInitialPentagonRectangle C R D _ _).symm)
  · obtain ⟨hD, hleft, hturn⟩ := (G.mem_rectanglePentagonTurnCuts C D).1 hD
    refine (G.mem_initialPentagonRectangleTurnCuts C _).2
      ⟨G.toInitialPentagonRectangle_mem_initialPentagonRectangleDecompositions C hD hleft hturn,
        ?_⟩
    simpa only [GridRectanglePentagonDecomposition.toInitialPentagonRectangle] using
      ⟨D.pentagon.right_eq, D.pentagon.turn_mem_cIco_bottom_top⟩
  · obtain ⟨hE, hright, hturn⟩ := (G.mem_initialPentagonRectangleTurnCuts C E).1 hE
    refine (G.mem_rectanglePentagonTurnCuts C _).2
      ⟨G.toRectanglePentagon_mem_rectanglePentagonDecompositions C hE hright hturn, ?_⟩
    simpa only [GridInitialPentagonRectangleDecomposition.toRectanglePentagon] using
      ⟨E.first_left_eq, E.first_turn_mem⟩

variable (x z) in
open scoped Classical in
/-- In the chain-map equation of the commutation map, the four families of decompositions cut at
the turn point can be removed: each counted decomposition of one family is matched, with the same
weight, by its reading on the other side of the equation. -/
theorem sum_rectanglePentagonWeight_add_sum_rectangleInitialPentagonWeight_eq_iff_sdiff_turnCuts
    [IsCancelAdd R] :
    (∑ D ∈ G.rectanglePentagonDecompositions C x z, G.rectanglePentagonWeight C R D) +
          ∑ D ∈ G.rectangleInitialPentagonDecompositions C x z,
            G.rectangleInitialPentagonWeight C R D =
        (∑ E ∈ G.pentagonRectangleDecompositions C x z, G.pentagonRectangleWeight C R E) +
          ∑ E ∈ G.initialPentagonRectangleDecompositions C x z,
            G.initialPentagonRectangleWeight C R E ↔
      (∑ D ∈ G.rectanglePentagonDecompositions C x z \ G.rectanglePentagonTurnCuts C x z,
          G.rectanglePentagonWeight C R D) +
          ∑ D ∈ G.rectangleInitialPentagonDecompositions C x z \
              G.rectangleInitialPentagonTurnCuts C x z,
            G.rectangleInitialPentagonWeight C R D =
        (∑ E ∈ G.pentagonRectangleDecompositions C x z \ G.pentagonRectangleTurnCuts C x z,
          G.pentagonRectangleWeight C R E) +
          ∑ E ∈ G.initialPentagonRectangleDecompositions C x z \
              G.initialPentagonRectangleTurnCuts C x z,
            G.initialPentagonRectangleWeight C R E := by
  rw [← Finset.sum_sdiff (s₁ := G.rectanglePentagonTurnCuts C x z)
      (fun D hD => ((G.mem_rectanglePentagonTurnCuts C D).1 hD).1),
    ← Finset.sum_sdiff (s₁ := G.rectangleInitialPentagonTurnCuts C x z)
      (fun D hD => ((G.mem_rectangleInitialPentagonTurnCuts C D).1 hD).1),
    ← Finset.sum_sdiff (s₁ := G.pentagonRectangleTurnCuts C x z)
      (fun E hE => ((G.mem_pentagonRectangleTurnCuts C E).1 hE).1),
    ← Finset.sum_sdiff (s₁ := G.initialPentagonRectangleTurnCuts C x z)
      (fun E hE => ((G.mem_initialPentagonRectangleTurnCuts C E).1 hE).1),
    G.sum_rectanglePentagonWeight_turnCuts_eq_sum_initialPentagonRectangleWeight C x z R,
    G.sum_rectangleInitialPentagonWeight_turnCuts_eq_sum_pentagonRectangleWeight C x z R]
  -- Both sides now carry the two matched totals, which cancel.
  have hcancel : ∀ p q r t u v : MvPolynomial (Fin n) R,
      p + u + (q + v) = r + v + (t + u) ↔ p + q = r + t := fun p q r t u v => by
    rw [add_add_add_comm, add_add_add_comm r, add_comm v u, add_right_cancel_iff]
  exact hcancel _ _ _ _ _ _

end GridDiagram

end TauCeti
