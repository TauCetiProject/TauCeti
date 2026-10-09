/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Pentagon
public import TauCeti.KnotTheory.Grid.Differential.Square.Decomposition

/-!
# Rectangle--pentagon decompositions for grid commutation

The chain-map equation for the pentagon map of a column commutation compares two kinds of
two-step domain. In one order, a rectangle in the original diagram is followed by a pentagon;
in the other, a pentagon is followed by a rectangle in the commuted diagram. This file packages
the two kinds of decomposition and rewrites the two matrix products in the chain-map equation as
sums over them.

For a validated column commutation `C` of `G`, write `G'` for the diagram obtained by swapping
the columns of `C`, and `Phi` for `GridDiagram.pentagonMap`. The coefficient of
`Phi (partial x)` at `z` is the sum over
`GridRectanglePentagonDecomposition C.column C.turnRow x z`; its weight is the rectangle weight,
renamed into the coefficient variables of `G'`, times the pentagon weight. The coefficient of
`partial' (Phi x)` is the sum over `GridPentagonRectangleDecomposition C.column C.turnRow x z`;
its weight is the pentagon weight times the rectangle weight in `G'`.

These are the terms of the chain-map equation in which the pentagon turns on its terminal side.
The commutation map `GridDiagram.commutationMap` also counts pentagons turning on their initial
side, and some composite domains here are matched only by decompositions involving those, so
these two finite sets cannot be matched with each other alone. Keeping the counting identities
here separate from the geometric pairing makes the target of the juxtaposition argument
explicit.

## Main definitions

* `TauCeti.GridRectanglePentagonDecomposition`: a rectangle followed by a pentagon.
* `TauCeti.GridPentagonRectangleDecomposition`: a pentagon followed by a rectangle.
* `TauCeti.GridRectanglePentagonDecomposition.toRectangleDecomposition` and
  `TauCeti.GridPentagonRectangleDecomposition.toRectangleDecomposition`: forget the distinguished
  turn point and retain the underlying pair of rectangles.
* `TauCeti.GridDiagram.rectanglePentagonDecompositions`: the first kind counted in the
  chain-map equation.
* `TauCeti.GridDiagram.pentagonRectangleDecompositions`: the second kind counted there.

## Main results

* `TauCeti.GridDiagram.sum_rename_unblockedCoefficient_mul_pentagonCoefficient` and
  `TauCeti.GridDiagram.sum_pentagonCoefficient_mul_unblockedCoefficient_swapColumns` rewrite the
  two matrix products as sums over composite domains.
* `TauCeti.GridDiagram.pentagonMap_unblockedDifferential_single_apply` and
  `TauCeti.GridDiagram.unblockedDifferential_pentagonMap_single_apply` identify those sums with
  the two sides of the chain-map equation on a grid-state generator.
* `TauCeti.GridDiagram.pentagonRectangleWeight_eq_rectanglePentagonWeight_of_val_add_val_eq`
  and `TauCeti.GridDiagram.rectanglePentagonWeight_eq_of_val_add_val_eq`: two composite domains
  covering the same squares with the same multiplicities, a rectangle of the commuted diagram read
  with its two commuted columns exchanged, have the same weight. They rest on
  `TauCeti.GridDiagram.rename_OMonomial_eq_prod_swapSquareWeight` and
  `TauCeti.GridDiagram.OMonomial_swapColumns_eq_prod_swapSquareWeight`, which write the renamed
  rectangle weight and the rectangle weight in the commuted diagram as products of the
  per-square weight `TauCeti.GridDiagram.swapSquareWeight`.
* `TauCeti.GridDiagram.mem_pentagonRectangleDecompositions_of_val_add_val_eq`: a pentagon
  followed by a rectangle of the commuted diagram, made of empty domains and covering the squares
  of a counted rectangle followed by a pentagon, is counted.

* `TauCeti.GridDiagram.rectanglePentagonWeight_eq_prod_OColumnsOfSquares_union` and
  `TauCeti.GridDiagram.pentagonRectangleWeight_eq_prod_OColumnsOfSquares_union`: when the
  constituent square domains are disjoint, the composite weight counts their covered
  `O`-columns once.

## References

The decomposition of the chain-map equation is the pentagon--rectangle juxtaposition argument in
Ozsvath--Stipsicz--Szabo, *Grid Homology for Knots and Links*, Section 5.1.
-/

public section

namespace TauCeti

/-- A two-step domain consisting of a rectangle from `x` to an intermediate grid state, followed
by a pentagon from that state to `z`. -/
abbrev GridRectanglePentagonDecomposition {n : ℕ} (a s : Fin n) (x z : GridState n) :=
  GridTwoStepDecomposition GridRectangleBetween (GridPentagonBetween a s) x z

namespace GridRectanglePentagonDecomposition

/-- The rectangle in a rectangle--pentagon decomposition. -/
abbrev rectangle {n : ℕ} {a s : Fin n} {x z : GridState n}
    (D : GridRectanglePentagonDecomposition a s x z) := D.first

/-- The pentagon in a rectangle--pentagon decomposition. -/
abbrev pentagon {n : ℕ} {a s : Fin n} {x z : GridState n}
    (D : GridRectanglePentagonDecomposition a s x z) := D.second

end GridRectanglePentagonDecomposition

/-- A two-step domain consisting of a pentagon from `x` to an intermediate grid state, followed
by a rectangle from that state to `z`. -/
abbrev GridPentagonRectangleDecomposition {n : ℕ} (a s : Fin n) (x z : GridState n) :=
  GridTwoStepDecomposition (GridPentagonBetween a s) GridRectangleBetween x z

namespace GridPentagonRectangleDecomposition

/-- The pentagon in a pentagon--rectangle decomposition. -/
abbrev pentagon {n : ℕ} {a s : Fin n} {x z : GridState n}
    (D : GridPentagonRectangleDecomposition a s x z) := D.first

/-- The rectangle in a pentagon--rectangle decomposition. -/
abbrev rectangle {n : ℕ} {a s : Fin n} {x z : GridState n}
    (D : GridPentagonRectangleDecomposition a s x z) := D.second

end GridPentagonRectangleDecomposition

private theorem rectangleDecomposition_fields_heq {n : ℕ} {x z : GridState n}
    {D E : GridRectangleDecomposition x z} (h : D = E) :
    HEq D.first E.first ∧ HEq D.second E.second := by
  subst E
  exact ⟨HEq.rfl, HEq.rfl⟩

namespace GridPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- Forget that the first domain of a pentagon--rectangle decomposition has a distinguished
turn point. -/
def toRectangleDecomposition (D : GridPentagonRectangleDecomposition a s x z) :
    GridRectangleDecomposition x z where
  middle := D.middle
  first := D.pentagon.toGridRectangleBetween
  second := D.rectangle

/-- Forgetting the pentagon turn point preserves the intermediate state. -/
@[simp]
theorem toRectangleDecomposition_middle (D : GridPentagonRectangleDecomposition a s x z) :
    D.toRectangleDecomposition.middle = D.middle := by
  unfold toRectangleDecomposition
  rfl

/-- The first underlying rectangle has the pentagon's initial side. -/
@[simp]
theorem toRectangleDecomposition_first_left (D : GridPentagonRectangleDecomposition a s x z) :
    D.toRectangleDecomposition.first.left = D.pentagon.left := by
  unfold toRectangleDecomposition
  rfl

/-- The first underlying rectangle has the pentagon's terminal side. -/
@[simp]
theorem toRectangleDecomposition_first_right (D : GridPentagonRectangleDecomposition a s x z) :
    D.toRectangleDecomposition.first.right = D.pentagon.right := by
  unfold toRectangleDecomposition
  rfl

/-- The first underlying toroidal rectangle is the pentagon's underlying rectangle. -/
@[simp]
theorem toRectangleDecomposition_first_toGridRectangle
    (D : GridPentagonRectangleDecomposition a s x z) :
    D.toRectangleDecomposition.first.toGridRectangle = D.pentagon.toGridRectangle := by
  unfold toRectangleDecomposition
  rfl

/-- The second underlying rectangle has the rectangle's initial side. -/
@[simp]
theorem toRectangleDecomposition_second_left (D : GridPentagonRectangleDecomposition a s x z) :
    D.toRectangleDecomposition.second.left = D.rectangle.left := by
  unfold toRectangleDecomposition
  rfl

/-- The second underlying rectangle has the rectangle's terminal side. -/
@[simp]
theorem toRectangleDecomposition_second_right (D : GridPentagonRectangleDecomposition a s x z) :
    D.toRectangleDecomposition.second.right = D.rectangle.right := by
  unfold toRectangleDecomposition
  rfl

/-- The second underlying toroidal rectangle is the decomposition's rectangle. -/
@[simp]
theorem toRectangleDecomposition_second_toGridRectangle
    (D : GridPentagonRectangleDecomposition a s x z) :
    D.toRectangleDecomposition.second.toGridRectangle = D.rectangle.toGridRectangle := by
  unfold toRectangleDecomposition
  rfl

/-- A pentagon--rectangle decomposition is determined by its underlying pair of rectangles. -/
theorem toRectangleDecomposition_injective :
    Function.Injective
      (toRectangleDecomposition : GridPentagonRectangleDecomposition a s x z → _) := by
  intro D E h
  have hmiddle := congrArg GridTwoStepDecomposition.middle h
  have hrectangle : HEq D.rectangle E.rectangle :=
    (rectangleDecomposition_fields_heq h).2
  have hpentagon : HEq D.pentagon E.pentagon :=
    Subsingleton.helim
      (congrArg (fun y => GridPentagonBetween a s x y) hmiddle) D.pentagon E.pentagon
  exact GridTwoStepDecomposition.ext hmiddle hpentagon hrectangle

end GridPentagonRectangleDecomposition

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- Forget that the second domain of a rectangle--pentagon decomposition has a distinguished
turn point. -/
def toRectangleDecomposition (D : GridRectanglePentagonDecomposition a s x z) :
    GridRectangleDecomposition x z where
  middle := D.middle
  first := D.rectangle
  second := D.pentagon.toGridRectangleBetween

/-- Forgetting the pentagon turn point preserves the intermediate state. -/
@[simp]
theorem toRectangleDecomposition_middle (D : GridRectanglePentagonDecomposition a s x z) :
    D.toRectangleDecomposition.middle = D.middle := by
  unfold toRectangleDecomposition
  rfl

/-- The first underlying rectangle has the rectangle's initial side. -/
@[simp]
theorem toRectangleDecomposition_first_left (D : GridRectanglePentagonDecomposition a s x z) :
    D.toRectangleDecomposition.first.left = D.rectangle.left := by
  unfold toRectangleDecomposition
  rfl

/-- The first underlying rectangle has the rectangle's terminal side. -/
@[simp]
theorem toRectangleDecomposition_first_right (D : GridRectanglePentagonDecomposition a s x z) :
    D.toRectangleDecomposition.first.right = D.rectangle.right := by
  unfold toRectangleDecomposition
  rfl

/-- The first underlying toroidal rectangle is the decomposition's rectangle. -/
@[simp]
theorem toRectangleDecomposition_first_toGridRectangle
    (D : GridRectanglePentagonDecomposition a s x z) :
    D.toRectangleDecomposition.first.toGridRectangle = D.rectangle.toGridRectangle := by
  unfold toRectangleDecomposition
  rfl

/-- The second underlying rectangle has the pentagon's initial side. -/
@[simp]
theorem toRectangleDecomposition_second_left (D : GridRectanglePentagonDecomposition a s x z) :
    D.toRectangleDecomposition.second.left = D.pentagon.left := by
  unfold toRectangleDecomposition
  rfl

/-- The second underlying rectangle has the pentagon's terminal side. -/
@[simp]
theorem toRectangleDecomposition_second_right (D : GridRectanglePentagonDecomposition a s x z) :
    D.toRectangleDecomposition.second.right = D.pentagon.right := by
  unfold toRectangleDecomposition
  rfl

/-- The second underlying toroidal rectangle is the pentagon's underlying rectangle. -/
@[simp]
theorem toRectangleDecomposition_second_toGridRectangle
    (D : GridRectanglePentagonDecomposition a s x z) :
    D.toRectangleDecomposition.second.toGridRectangle = D.pentagon.toGridRectangle := by
  unfold toRectangleDecomposition
  rfl

/-- A rectangle--pentagon decomposition is determined by its underlying pair of rectangles. -/
theorem toRectangleDecomposition_injective :
    Function.Injective
      (toRectangleDecomposition : GridRectanglePentagonDecomposition a s x z → _) := by
  intro D E h
  have hmiddle := congrArg GridTwoStepDecomposition.middle h
  have hrectangle : HEq D.rectangle E.rectangle :=
    (rectangleDecomposition_fields_heq h).1
  have hpentagon : HEq D.pentagon E.pentagon :=
    Subsingleton.helim
      (congrArg (fun y => GridPentagonBetween a s y z) hmiddle) D.pentagon E.pentagon
  exact GridTwoStepDecomposition.ext hmiddle hrectangle hpentagon

end GridRectanglePentagonDecomposition

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

local notation "b" => finRotate n C.column

/-- The rectangle--pentagon decompositions counted by the coefficient of the pentagon map after
the original differential. -/
noncomputable def rectanglePentagonDecompositions (x z : GridState n) :
    Finset (GridRectanglePentagonDecomposition C.column C.turnRow x z) :=
  GridTwoStepDecomposition.decompositionsOf G.unblockedRectangles
    (fun u v => G.pentagons C u v) x z

/-- Membership in the counted rectangle--pentagon decompositions is membership of the rectangle
in the original differential and of the pentagon in the pentagon map. -/
@[simp]
theorem mem_rectanglePentagonDecompositions {x z : GridState n}
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z) :
    D ∈ G.rectanglePentagonDecompositions C x z ↔
      D.rectangle ∈ G.unblockedRectangles x D.middle ∧
        D.pentagon ∈ G.pentagons C D.middle z := by
  classical
  simp [rectanglePentagonDecompositions]

/-- The pentagon--rectangle decompositions counted by the coefficient of the commuted
differential after the pentagon map. -/
noncomputable def pentagonRectangleDecompositions (x z : GridState n) :
    Finset (GridPentagonRectangleDecomposition C.column C.turnRow x z) :=
  GridTwoStepDecomposition.decompositionsOf (fun u v => G.pentagons C u v)
    (G.swapColumns C.column b).unblockedRectangles x z

/-- Membership in the counted pentagon--rectangle decompositions is membership of the pentagon
in the pentagon map and of the rectangle in the commuted differential. -/
@[simp]
theorem mem_pentagonRectangleDecompositions {x z : GridState n}
    (D : GridPentagonRectangleDecomposition C.column C.turnRow x z) :
    D ∈ G.pentagonRectangleDecompositions C x z ↔
      D.pentagon ∈ G.pentagons C x D.middle ∧
        D.rectangle ∈ (G.swapColumns C.column b).unblockedRectangles D.middle z := by
  classical
  simp [pentagonRectangleDecompositions]

section Weights

variable (R : Type*) [CommSemiring R]

/-- The weight of a rectangle followed by a pentagon. The rectangle coefficient is renamed by
the column swap because the pentagon map is semilinear into the coefficient ring of the commuted
diagram. -/
noncomputable def rectanglePentagonWeight {x z : GridState n}
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z) :
    MvPolynomial (Fin n) R :=
  MvPolynomial.rename (Equiv.swap C.column b)
      (G.OMonomial R D.rectangle.toGridRectangle) *
    G.pentagonWeight R C D.pentagon

/-- The rectangle--pentagon weight is the renamed rectangle weight times the pentagon weight. -/
theorem rectanglePentagonWeight_def {x z : GridState n}
    (D : GridRectanglePentagonDecomposition C.column C.turnRow x z) :
    G.rectanglePentagonWeight C R D =
      MvPolynomial.rename (Equiv.swap C.column b)
          (G.OMonomial R D.rectangle.toGridRectangle) *
        G.pentagonWeight R C D.pentagon :=
  (rfl)

/-- The weight of a pentagon followed by a rectangle in the commuted diagram. -/
noncomputable def pentagonRectangleWeight {x z : GridState n}
    (D : GridPentagonRectangleDecomposition C.column C.turnRow x z) :
    MvPolynomial (Fin n) R :=
  G.pentagonWeight R C D.pentagon *
    (G.swapColumns C.column b).OMonomial R D.rectangle.toGridRectangle

/-- The pentagon--rectangle weight is the pentagon weight times the rectangle weight in the
commuted diagram. -/
theorem pentagonRectangleWeight_def {x z : GridState n}
    (D : GridPentagonRectangleDecomposition C.column C.turnRow x z) :
    G.pentagonRectangleWeight C R D =
      G.pentagonWeight R C D.pentagon *
        (G.swapColumns C.column b).OMonomial R D.rectangle.toGridRectangle :=
  (rfl)

/-- The weight of a square in a column commutation of the columns `i` and `j`: the variable of
the commuted column of its `O`-marking, and `1` on unmarked squares. -/
noncomputable def swapSquareWeight (i j : Fin n) (p : Fin n × Fin n) :
    MvPolynomial (Fin n) R :=
  if p ∈ G.OSet then MvPolynomial.X (Equiv.swap i j p.1) else 1

/-- The weight of a square is the swapped variable of its column at an `O`-marking and `1`
elsewhere. -/
theorem swapSquareWeight_def (i j : Fin n) (p : Fin n × Fin n) :
    G.swapSquareWeight R i j p =
      if p ∈ G.OSet then MvPolynomial.X (Equiv.swap i j p.1) else 1 :=
  (rfl)

/-- The renamed `O`-monomial of a rectangle of the original diagram, square by square. -/
theorem rename_OMonomial_eq_prod_swapSquareWeight (i j : Fin n) (r : GridRectangle n) :
    MvPolynomial.rename (Equiv.swap i j) (G.OMonomial R r) =
      ∏ p ∈ r.coveredSquares, G.swapSquareWeight R i j p := by
  rw [G.OMonomial_eq_prod_coveredSquares R, map_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  unfold swapSquareWeight
  split_ifs <;> simp

/-- The `O`-monomial of a rectangle of the commuted diagram, square by square: a square of the
commuted diagram carries the marking of the square of the original diagram in the swapped
column. -/
theorem OMonomial_swapColumns_eq_prod_swapSquareWeight (i j : Fin n)
    (r : GridRectangle n) :
    (G.swapColumns i j).OMonomial R r =
      ∏ p ∈ r.coveredSquares.map
        ((Equiv.swap i j).prodCongr (Equiv.refl (Fin n))).toEmbedding,
        G.swapSquareWeight R i j p := by
  rw [(G.swapColumns i j).OMonomial_eq_prod_coveredSquares R, Finset.prod_map]
  refine Finset.prod_congr rfl fun p _ => ?_
  obtain ⟨c, t⟩ := p
  simp only [swapSquareWeight, mem_OSet_swapColumns, Equiv.coe_toEmbedding,
    Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, Equiv.swap_apply_self]

/-- The weight of a pentagon, square by square. -/
private theorem pentagonWeight_eq_prod_swapSquareWeight {x y : GridState n}
    (P : GridPentagonBetween C.column C.turnRow x y) :
    G.pentagonWeight R C P =
      ∏ p ∈ P.coveredSquares, G.swapSquareWeight R C.column (finRotate n C.column) p :=
  G.pentagonWeight_eq_prod_coveredSquares R C P

/-- When the two domains have disjoint covered squares, their composite weight counts each
covered O-marking once, in the variables of the commuted diagram. -/
theorem rectanglePentagonWeight_eq_prod_OColumnsOfSquares_union
    {x z : GridState n} (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (h : Disjoint D.rectangle.toGridRectangle.coveredSquares D.pentagon.coveredSquares) :
    G.rectanglePentagonWeight C R D =
      ∏ c ∈ G.OColumnsOfSquares
        (D.rectangle.toGridRectangle.coveredSquares ∪ D.pentagon.coveredSquares),
        MvPolynomial.X (Equiv.swap C.column b c) := by
  rw [rectanglePentagonWeight_def, rename_OMonomial_eq_prod_swapSquareWeight,
    pentagonWeight_eq_prod_swapSquareWeight, ← Finset.prod_union h]
  simp only [swapSquareWeight]
  exact G.prod_ite_OSet_eq_prod_OColumnsOfSquares
    (fun c => (MvPolynomial.X (Equiv.swap C.column b c) : MvPolynomial (Fin n) R)) _

/-- When the pentagon and the rectangle read back in the original columns have disjoint
covered squares, their composite weight counts each covered O-marking once, in the variables
of the commuted diagram. -/
theorem pentagonRectangleWeight_eq_prod_OColumnsOfSquares_union
    {x z : GridState n} (D : GridPentagonRectangleDecomposition C.column C.turnRow x z)
    (h : Disjoint D.pentagon.coveredSquares
      (D.rectangle.toGridRectangle.coveredSquares.map
        ((Equiv.swap C.column b).prodCongr (Equiv.refl (Fin n))).toEmbedding)) :
    G.pentagonRectangleWeight C R D =
      ∏ c ∈ G.OColumnsOfSquares (D.pentagon.coveredSquares ∪
        D.rectangle.toGridRectangle.coveredSquares.map
          ((Equiv.swap C.column b).prodCongr (Equiv.refl (Fin n))).toEmbedding),
        MvPolynomial.X (Equiv.swap C.column b c) := by
  rw [pentagonRectangleWeight_def, pentagonWeight_eq_prod_swapSquareWeight,
    OMonomial_swapColumns_eq_prod_swapSquareWeight, ← Finset.prod_union h]
  simp only [swapSquareWeight]
  exact G.prod_ite_OSet_eq_prod_OColumnsOfSquares
    (fun c => (MvPolynomial.X (Equiv.swap C.column b c) : MvPolynomial (Fin n) R)) _

/-- A pentagon followed by a rectangle of the commuted diagram has the weight of a rectangle
followed by a pentagon when the two composite domains cover the same squares with the same
multiplicities, the squares of the rectangle of the commuted diagram being read in the
original diagram, that is with the two commuted columns exchanged. -/
theorem pentagonRectangleWeight_eq_rectanglePentagonWeight_of_val_add_val_eq
    {x z : GridState n} (D : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (E : GridPentagonRectangleDecomposition C.column C.turnRow x z)
    (h : E.pentagon.coveredSquares.val +
        (E.rectangle.toGridRectangle.coveredSquares.map
          ((Equiv.swap C.column b).prodCongr (Equiv.refl (Fin n))).toEmbedding).val =
      D.rectangle.toGridRectangle.coveredSquares.val + D.pentagon.coveredSquares.val) :
    G.pentagonRectangleWeight C R E = G.rectanglePentagonWeight C R D := by
  rw [pentagonRectangleWeight_def, rectanglePentagonWeight_def,
    pentagonWeight_eq_prod_swapSquareWeight, pentagonWeight_eq_prod_swapSquareWeight,
    OMonomial_swapColumns_eq_prod_swapSquareWeight, rename_OMonomial_eq_prod_swapSquareWeight]
  simp only [Finset.prod_eq_multiset_prod, ← Multiset.prod_add, ← Multiset.map_add, h]

/-- Two rectangle--pentagon decompositions have the same weight when they cover the same squares
with the same multiplicities. -/
theorem rectanglePentagonWeight_eq_of_val_add_val_eq
    {x z : GridState n} (D D' : GridRectanglePentagonDecomposition C.column C.turnRow x z)
    (h : D'.rectangle.toGridRectangle.coveredSquares.val + D'.pentagon.coveredSquares.val =
      D.rectangle.toGridRectangle.coveredSquares.val + D.pentagon.coveredSquares.val) :
    G.rectanglePentagonWeight C R D' = G.rectanglePentagonWeight C R D := by
  rw [rectanglePentagonWeight_def, rectanglePentagonWeight_def,
    pentagonWeight_eq_prod_swapSquareWeight, pentagonWeight_eq_prod_swapSquareWeight,
    rename_OMonomial_eq_prod_swapSquareWeight, rename_OMonomial_eq_prod_swapSquareWeight]
  simp only [Finset.prod_eq_multiset_prod, ← Multiset.prod_add, ← Multiset.map_add, h]

/-- Two pentagon--rectangle decompositions have the same weight when their composite domains
cover the same squares with multiplicity, reading the rectangles of the commuted diagram
in the original diagram by exchanging the two commuted columns. -/
theorem pentagonRectangleWeight_eq_of_val_add_val_eq
    {x z : GridState n} (D D' : GridPentagonRectangleDecomposition C.column C.turnRow x z)
    (h : D'.pentagon.coveredSquares.val +
        (D'.rectangle.toGridRectangle.coveredSquares.map
          ((Equiv.swap C.column b).prodCongr (Equiv.refl (Fin n))).toEmbedding).val =
      D.pentagon.coveredSquares.val +
        (D.rectangle.toGridRectangle.coveredSquares.map
          ((Equiv.swap C.column b).prodCongr (Equiv.refl (Fin n))).toEmbedding).val) :
    G.pentagonRectangleWeight C R D' = G.pentagonRectangleWeight C R D := by
  rw [pentagonRectangleWeight_def, pentagonRectangleWeight_def,
    pentagonWeight_eq_prod_swapSquareWeight, pentagonWeight_eq_prod_swapSquareWeight,
    OMonomial_swapColumns_eq_prod_swapSquareWeight, OMonomial_swapColumns_eq_prod_swapSquareWeight]
  simp only [Finset.prod_eq_multiset_prod, ← Multiset.prod_add, ← Multiset.map_add, h]

/-- A pentagon followed by a rectangle of the commuted diagram is counted when its two domains are
empty and its composite domain covers, with multiplicity, the squares of a counted rectangle
followed by a pentagon, the rectangle of the commuted diagram being read in the original diagram:
every square it covers then avoids the `X`-markings. -/
theorem mem_pentagonRectangleDecompositions_of_val_add_val_eq {x z : GridState n}
    {D : GridRectanglePentagonDecomposition C.column C.turnRow x z}
    (hD : D ∈ G.rectanglePentagonDecompositions C x z)
    {E : GridPentagonRectangleDecomposition C.column C.turnRow x z}
    (hpentagon : E.pentagon.IsEmpty) (hrectangle : E.rectangle.IsEmpty)
    (h : E.pentagon.coveredSquares.val +
        (E.rectangle.toGridRectangle.coveredSquares.map
          ((Equiv.swap C.column b).prodCongr (Equiv.refl (Fin n))).toEmbedding).val =
      D.rectangle.toGridRectangle.coveredSquares.val + D.pentagon.coveredSquares.val) :
    E ∈ G.pentagonRectangleDecompositions C x z := by
  rw [mem_rectanglePentagonDecompositions, mem_unblockedRectangles, mem_pentagons] at hD
  -- A square of the new domain is a square of the original domain, which avoids `X`.
  have hX : Disjoint (E.pentagon.coveredSquares ∪ E.rectangle.toGridRectangle.coveredSquares.map
      ((Equiv.swap C.column b).prodCongr (Equiv.refl (Fin n))).toEmbedding) G.XSet := by
    refine Finset.disjoint_left.mpr fun p hp hpX => ?_
    have hmem : p ∈ D.rectangle.toGridRectangle.coveredSquares.val +
        D.pentagon.coveredSquares.val := by
      rw [← h, Multiset.mem_add]
      simpa only [Finset.mem_union, Finset.mem_val] using hp
    rcases Multiset.mem_add.mp hmem with hp' | hp'
    · exact Finset.disjoint_left.mp hD.1.2 hp' hpX
    · exact Finset.disjoint_left.mp hD.2.2 hp' hpX
  rw [mem_pentagonRectangleDecompositions, mem_pentagons,
    (G.swapColumns C.column b).mem_unblockedRectangles, ← G.disjoint_map_swapColumns_XSet_iff]
  exact ⟨⟨hpentagon, (Finset.disjoint_union_left.mp hX).1⟩, hrectangle,
    (Finset.disjoint_union_left.mp hX).2⟩

/-- The matrix product for the pentagon map after the original differential is the sum of the
weights of the counted rectangle--pentagon decompositions. -/
theorem sum_rename_unblockedCoefficient_mul_pentagonCoefficient (x z : GridState n) :
    ∑ y : GridState n,
        MvPolynomial.rename (Equiv.swap C.column b) (G.unblockedCoefficient R x y) *
          G.pentagonCoefficient R C y z =
      ∑ D ∈ G.rectanglePentagonDecompositions C x z,
        G.rectanglePentagonWeight C R D := by
  have hstep : ∀ y : GridState n,
      MvPolynomial.rename (Equiv.swap C.column b) (G.unblockedCoefficient R x y) *
          G.pentagonCoefficient R C y z =
        ∑ r ∈ G.unblockedRectangles x y, ∑ P ∈ G.pentagons C y z,
          MvPolynomial.rename (Equiv.swap C.column b) (G.OMonomial R r.toGridRectangle) *
            G.pentagonWeight R C P := fun y => by
    rw [G.unblockedCoefficient_def R x y, map_sum, G.pentagonCoefficient_def R C y z,
      Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => hstep y]
  exact (GridTwoStepDecomposition.sum_decompositionsOf
    G.unblockedRectangles (fun u v => G.pentagons C u v)
    (fun _ r P => MvPolynomial.rename (Equiv.swap C.column b)
      (G.OMonomial R r.toGridRectangle) * G.pentagonWeight R C P)).symm

/-- The matrix product for the commuted differential after the pentagon map is the sum of the
weights of the counted pentagon--rectangle decompositions. -/
theorem sum_pentagonCoefficient_mul_unblockedCoefficient_swapColumns (x z : GridState n) :
    ∑ y : GridState n, G.pentagonCoefficient R C x y *
        (G.swapColumns C.column b).unblockedCoefficient R y z =
      ∑ D ∈ G.pentagonRectangleDecompositions C x z,
        G.pentagonRectangleWeight C R D := by
  have hstep : ∀ y : GridState n,
      G.pentagonCoefficient R C x y *
          (G.swapColumns C.column b).unblockedCoefficient R y z =
        ∑ P ∈ G.pentagons C x y,
          ∑ r ∈ (G.swapColumns C.column b).unblockedRectangles y z,
            G.pentagonWeight R C P *
              (G.swapColumns C.column b).OMonomial R r.toGridRectangle := fun y => by
    rw [G.pentagonCoefficient_def R C x y,
      (G.swapColumns C.column b).unblockedCoefficient_def R y z, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl fun y (_ : y ∈ Finset.univ) => hstep y]
  exact (GridTwoStepDecomposition.sum_decompositionsOf
    (fun u v => G.pentagons C u v)
    (G.swapColumns C.column b).unblockedRectangles
    (fun _ P r => G.pentagonWeight R C P *
      (G.swapColumns C.column b).OMonomial R r.toGridRectangle)).symm

/-- On a grid-state generator, the coefficient of the pentagon map after the original
differential is the rectangle--pentagon decomposition sum. -/
theorem pentagonMap_unblockedDifferential_single_apply (x z : GridState n) :
    G.pentagonMap R C (G.unblockedDifferential R (Finsupp.single x 1)) z =
      ∑ D ∈ G.rectanglePentagonDecompositions C x z,
        G.rectanglePentagonWeight C R D := by
  rw [G.pentagonMap_apply_apply R C, G.unblockedDifferential_single,
    Finsupp.sum_fintype _ _ fun _ => by simp]
  simp_rw [G.unblockedDifferentialOnGenerator_apply R x]
  exact G.sum_rename_unblockedCoefficient_mul_pentagonCoefficient C R x z

/-- On a grid-state generator, the coefficient of the commuted differential after the pentagon
map is the pentagon--rectangle decomposition sum. -/
theorem unblockedDifferential_pentagonMap_single_apply (x z : GridState n) :
    (G.swapColumns C.column b).unblockedDifferential R
        (G.pentagonMap R C (Finsupp.single x 1)) z =
      ∑ D ∈ G.pentagonRectangleDecompositions C x z,
        G.pentagonRectangleWeight C R D := by
  rw [G.pentagonMap_single R C x 1, map_one, one_smul,
    (G.swapColumns C.column b).unblockedDifferential_apply_apply R,
    Finsupp.sum_fintype _ _ fun _ => zero_mul _]
  simp_rw [G.pentagonMapOnGenerator_apply R C x]
  exact G.sum_pentagonCoefficient_mul_unblockedCoefficient_swapColumns C R x z

/-- The pentagon map commutes with the differentials on a grid-state generator exactly when the
two finite sums of composite-domain weights agree at every target state. This is the precise
finite combinatorial criterion discharged by the rectangle--pentagon juxtaposition pairing. -/
theorem pentagonMap_unblockedDifferential_single_eq_iff (x : GridState n) :
    G.pentagonMap R C (G.unblockedDifferential R (Finsupp.single x 1)) =
        (G.swapColumns C.column b).unblockedDifferential R
          (G.pentagonMap R C (Finsupp.single x 1)) ↔
      ∀ z : GridState n,
        (∑ D ∈ G.rectanglePentagonDecompositions C x z,
            G.rectanglePentagonWeight C R D) =
          ∑ D ∈ G.pentagonRectangleDecompositions C x z,
            G.pentagonRectangleWeight C R D := by
  constructor
  · intro h z
    have hz := DFunLike.congr_fun h z
    rw [G.pentagonMap_unblockedDifferential_single_apply C R x z,
      G.unblockedDifferential_pentagonMap_single_apply C R x z] at hz
    exact hz
  · intro h
    apply Finsupp.ext
    intro z
    rw [G.pentagonMap_unblockedDifferential_single_apply C R x z,
      G.unblockedDifferential_pentagonMap_single_apply C R x z]
    exact h z

end Weights

end GridDiagram

end TauCeti
