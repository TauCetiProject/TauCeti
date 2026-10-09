/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import TauCeti.KnotTheory.Grid.Commutation.Pentagon
public import TauCeti.KnotTheory.Grid.Differential.Square.Decomposition
public import TauCeti.KnotTheory.Grid.Differential.Square.Repartition

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
* `TauCeti.GridDiagram.mem_pentagonRectangleDecompositions_of_forall_notMem_XSet`: a pentagon
  followed by a rectangle of the commuted diagram, made of empty domains whose squares avoid the
  `X`-markings, is counted.
* `TauCeti.GridDiagram.mem_pentagonRectangleDecompositions_of_val_add_val_eq_pentagonRectangle`:
  a pentagon followed by a rectangle of the commuted diagram, made of empty domains and covering
  the squares of another counted pentagon followed by a rectangle, is counted.
* `TauCeti.GridDiagram.mem_pentagonRectangleDecompositions_of_val_add_val_eq`: a pentagon
  followed by a rectangle of the commuted diagram, made of empty domains and covering the squares
  of a counted rectangle followed by a pentagon, is counted.
  `TauCeti.GridDiagram.mem_rectanglePentagonDecompositions_of_val_add_val_eq` is the same
  statement for a rectangle followed by a pentagon.
* `TauCeti.GridRectanglePentagonDecomposition.coveredSquares_val_add_val_eq_of_isRepartition`:
  the column balance criterion for a rectangle--pentagon and a pentagon--rectangle domain to cover
  the same squares with the same multiplicities.
* `TauCeti.GridRectanglePentagonDecomposition.
  coveredSquares_val_add_val_eq_of_isRepartition_of_bottom_eq`: two rectangle--pentagon domains
  repartitioning the same squares cover the same squares with the same multiplicities when their
  pentagons have the same bottom row.

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
structure GridRectanglePentagonDecomposition {n : ℕ} (a s : Fin n)
    (x z : GridState n) where
  /-- The grid state at which the rectangle and pentagon meet. -/
  middle : GridState n
  /-- The first domain, an oriented rectangle from the source to the intermediate state. -/
  rectangle : GridRectangleBetween x middle
  /-- The second domain, a pentagon from the intermediate state to the target. -/
  pentagon : GridPentagonBetween a s middle z

/-- A two-step domain consisting of a pentagon from `x` to an intermediate grid state, followed
by a rectangle from that state to `z`. -/
structure GridPentagonRectangleDecomposition {n : ℕ} (a s : Fin n)
    (x z : GridState n) where
  /-- The grid state at which the pentagon and rectangle meet. -/
  middle : GridState n
  /-- The first domain, a pentagon from the source to the intermediate state. -/
  pentagon : GridPentagonBetween a s x middle
  /-- The second domain, an oriented rectangle from the intermediate state to the target. -/
  rectangle : GridRectangleBetween middle z

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- Two rectangle--pentagon decompositions are equal when their intermediate states and their two
constituent domains agree. -/
@[ext]
theorem ext {D E : GridRectanglePentagonDecomposition a s x z}
    (hmiddle : D.middle = E.middle) (hrectangle : HEq D.rectangle E.rectangle)
    (hpentagon : HEq D.pentagon E.pentagon) : D = E := by
  cases D
  cases E
  simp_all

private def sigmaEquiv :
    GridRectanglePentagonDecomposition a s x z ≃
      (Σ y : GridState n,
        Σ _rectangle : GridRectangleBetween x y, GridPentagonBetween a s y z) where
  toFun D := ⟨D.middle, D.rectangle, D.pentagon⟩
  invFun D := ⟨D.1, D.2.1, D.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The finite set of rectangle--pentagon decompositions selected by prescribed finite families
of rectangles and pentagons. -/
noncomputable def decompositionsOf
    (rectangles : ∀ u v : GridState n, Finset (GridRectangleBetween u v))
    (pentagons : ∀ u v : GridState n, Finset (GridPentagonBetween a s u v))
    (x z : GridState n) : Finset (GridRectanglePentagonDecomposition a s x z) := by
  classical
  exact ((Finset.univ.sigma fun y => (rectangles x y).sigma fun _ => pentagons y z).map
    (sigmaEquiv (a := a) (s := s) (x := x) (z := z)).symm.toEmbedding)

/-- A rectangle--pentagon decomposition belongs to `decompositionsOf` exactly when its two
constituent domains belong to the prescribed families. -/
@[simp]
theorem mem_decompositionsOf
    (rectangles : ∀ u v : GridState n, Finset (GridRectangleBetween u v))
    (pentagons : ∀ u v : GridState n, Finset (GridPentagonBetween a s u v))
    (x z : GridState n) (D : GridRectanglePentagonDecomposition a s x z) :
    D ∈ decompositionsOf rectangles pentagons x z ↔
      D.rectangle ∈ rectangles x D.middle ∧ D.pentagon ∈ pentagons D.middle z := by
  classical
  simp [decompositionsOf, sigmaEquiv]

/-- Summing over rectangle--pentagon decompositions is the iterated sum over the intermediate
state and the two constituent domains. -/
theorem sum_decompositionsOf {M : Type*} [AddCommMonoid M]
    (rectangles : ∀ u v : GridState n, Finset (GridRectangleBetween u v))
    (pentagons : ∀ u v : GridState n, Finset (GridPentagonBetween a s u v))
    (x z : GridState n)
    (w : ∀ y, GridRectangleBetween x y → GridPentagonBetween a s y z → M) :
    ∑ D ∈ decompositionsOf rectangles pentagons x z, w D.middle D.rectangle D.pentagon =
      ∑ y, ∑ r ∈ rectangles x y, ∑ P ∈ pentagons y z, w y r P := by
  classical
  simp [decompositionsOf, sigmaEquiv, Finset.sum_sigma']

end GridRectanglePentagonDecomposition

namespace GridPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- Two pentagon--rectangle decompositions are equal when their intermediate states and their two
constituent domains agree. -/
@[ext]
theorem ext {D E : GridPentagonRectangleDecomposition a s x z}
    (hmiddle : D.middle = E.middle) (hpentagon : HEq D.pentagon E.pentagon)
    (hrectangle : HEq D.rectangle E.rectangle) : D = E := by
  cases D
  cases E
  simp_all

private def sigmaEquiv :
    GridPentagonRectangleDecomposition a s x z ≃
      (Σ y : GridState n,
        Σ _pentagon : GridPentagonBetween a s x y, GridRectangleBetween y z) where
  toFun D := ⟨D.middle, D.pentagon, D.rectangle⟩
  invFun D := ⟨D.1, D.2.1, D.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The finite set of pentagon--rectangle decompositions selected by prescribed finite families
of pentagons and rectangles. -/
noncomputable def decompositionsOf
    (pentagons : ∀ u v : GridState n, Finset (GridPentagonBetween a s u v))
    (rectangles : ∀ u v : GridState n, Finset (GridRectangleBetween u v))
    (x z : GridState n) : Finset (GridPentagonRectangleDecomposition a s x z) := by
  classical
  exact ((Finset.univ.sigma fun y => (pentagons x y).sigma fun _ => rectangles y z).map
    (sigmaEquiv (a := a) (s := s) (x := x) (z := z)).symm.toEmbedding)

/-- A pentagon--rectangle decomposition belongs to `decompositionsOf` exactly when its two
constituent domains belong to the prescribed families. -/
@[simp]
theorem mem_decompositionsOf
    (pentagons : ∀ u v : GridState n, Finset (GridPentagonBetween a s u v))
    (rectangles : ∀ u v : GridState n, Finset (GridRectangleBetween u v))
    (x z : GridState n) (D : GridPentagonRectangleDecomposition a s x z) :
    D ∈ decompositionsOf pentagons rectangles x z ↔
      D.pentagon ∈ pentagons x D.middle ∧ D.rectangle ∈ rectangles D.middle z := by
  classical
  simp [decompositionsOf, sigmaEquiv]

/-- Summing over pentagon--rectangle decompositions is the iterated sum over the intermediate
state and the two constituent domains. -/
theorem sum_decompositionsOf {M : Type*} [AddCommMonoid M]
    (pentagons : ∀ u v : GridState n, Finset (GridPentagonBetween a s u v))
    (rectangles : ∀ u v : GridState n, Finset (GridRectangleBetween u v))
    (x z : GridState n)
    (w : ∀ y, GridPentagonBetween a s x y → GridRectangleBetween y z → M) :
    ∑ D ∈ decompositionsOf pentagons rectangles x z, w D.middle D.pentagon D.rectangle =
      ∑ y, ∑ P ∈ pentagons x y, ∑ r ∈ rectangles y z, w y P r := by
  classical
  simp [decompositionsOf, sigmaEquiv, Finset.sum_sigma']

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
  have hmiddle := congrArg GridRectangleDecomposition.middle h
  have hrectangle : HEq D.rectangle E.rectangle :=
    (rectangleDecomposition_fields_heq h).2
  have hpentagon : HEq D.pentagon E.pentagon :=
    Subsingleton.helim
      (congrArg (fun y => GridPentagonBetween a s x y) hmiddle) D.pentagon E.pentagon
  exact GridPentagonRectangleDecomposition.ext hmiddle hpentagon hrectangle

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
  have hmiddle := congrArg GridRectangleDecomposition.middle h
  have hrectangle : HEq D.rectangle E.rectangle :=
    (rectangleDecomposition_fields_heq h).1
  have hpentagon : HEq D.pentagon E.pentagon :=
    Subsingleton.helim
      (congrArg (fun y => GridPentagonBetween a s y z) hmiddle) D.pentagon E.pentagon
  exact GridRectanglePentagonDecomposition.ext hmiddle hrectangle hpentagon

/-- A pentagon followed by a rectangle and a rectangle followed by a pentagon have the same
composite domain, squares counted with multiplicity and the columns `a` and `finRotate n a` of the
second rectangle exchanged, when their underlying rectangles repartition the same squares and the
two columns balance: at every row `t`, the second rectangle covers `(a, t)` and `t` lies between
the new pentagon's bottom row and the turn row as often as the second rectangle covers
`(finRotate n a, t)` and `t` lies between the original pentagon's bottom row and the turn row. -/
theorem coveredSquares_val_add_val_eq_of_isRepartition
    (D : GridRectanglePentagonDecomposition a s x z)
    (E : GridPentagonRectangleDecomposition a s x z)
    (hrep : D.toRectangleDecomposition.IsRepartition E.toRectangleDecomposition)
    (hcol : ∀ t : Fin n,
      ((if (a, t) ∈ E.rectangle.toGridRectangle.coveredSquares then 1 else 0) +
          if t ∈ Grid.cIco E.pentagon.bottom s then 1 else 0 : ℕ) =
        (if (finRotate n a, t) ∈ E.rectangle.toGridRectangle.coveredSquares then 1 else 0) +
          if t ∈ Grid.cIco D.pentagon.bottom s then 1 else 0) :
    E.pentagon.coveredSquares.val +
        (E.rectangle.toGridRectangle.coveredSquares.map
          ((Equiv.swap a (finRotate n a)).prodCongr (Equiv.refl (Fin n))).toEmbedding).val =
      D.rectangle.toGridRectangle.coveredSquares.val + D.pentagon.coveredSquares.val := by
  have hrep' := fun q => congrArg (Multiset.count q) hrep.val_add_val_eq
  simp only [Multiset.count_add, Multiset.count_eq_of_nodup (Finset.nodup _), Finset.mem_val,
    toRectangleDecomposition_first_toGridRectangle,
    toRectangleDecomposition_second_toGridRectangle,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_first_toGridRectangle,
    GridPentagonRectangleDecomposition.toRectangleDecomposition_second_toGridRectangle] at hrep'
  refine Multiset.ext.mpr fun p => ?_
  simp only [Multiset.count_add, Multiset.count_eq_of_nodup (Finset.nodup _), Finset.mem_val,
    Finset.mem_map_equiv, Equiv.prodCongr_symm, Equiv.symm_swap, Equiv.refl_symm,
    Equiv.prodCongr_apply]
  obtain ⟨c, t⟩ := p
  simp only [Prod.map_apply, Equiv.refl_apply]
  by_cases hca : c = a
  · subst hca
    have h1 := hrep' (c, t)
    have h2 := hrep' (finRotate n c, t)
    have h3 := hcol t
    have h4 := Grid.ite_mem_cIco_eq_add_add E.pentagon.turn_mem_cIco_bottom_top t
    have h5 := Grid.ite_mem_cIco_eq_add_add D.pentagon.turn_mem_cIco_bottom_top t
    simp only [GridPentagonBetween.mk_mem_coveredSquares_left_column,
      GridPentagonBetween.mk_mem_toGridRectangle_coveredSquares_left_column,
      GridPentagonBetween.mk_notMem_toGridRectangle_coveredSquares_right_column,
      Equiv.swap_apply_left, ↓reduceIte, zero_add, add_zero] at h1 h2 ⊢
    omega
  by_cases hcb : c = finRotate n a
  · subst hcb
    have h2 := hrep' (finRotate n a, t)
    have h3 := hcol t
    simp only [GridPentagonBetween.mk_mem_coveredSquares_right_column,
      GridPentagonBetween.mk_notMem_toGridRectangle_coveredSquares_right_column,
      Equiv.swap_apply_right, ↓reduceIte, zero_add, add_zero] at h2 ⊢
    omega
  · have h := hrep' (c, t)
    simp only [Equiv.swap_apply_of_ne_of_ne hca hcb,
      E.pentagon.mem_coveredSquares_iff_of_ne (p := (c, t)) hca hcb,
      D.pentagon.mem_coveredSquares_iff_of_ne (p := (c, t)) hca hcb]
    omega

/-- Two rectangle--pentagon decompositions cover the same squares with the same multiplicities
when their underlying rectangle decompositions are repartitions of each other and their pentagons
have the same bottom row. -/
theorem coveredSquares_val_add_val_eq_of_isRepartition_of_bottom_eq
    (D D' : GridRectanglePentagonDecomposition a s x z)
    (hrep : D.toRectangleDecomposition.IsRepartition D'.toRectangleDecomposition)
    (hbottom : D'.pentagon.bottom = D.pentagon.bottom) :
    D'.rectangle.toGridRectangle.coveredSquares.val + D'.pentagon.coveredSquares.val =
      D.rectangle.toGridRectangle.coveredSquares.val + D.pentagon.coveredSquares.val := by
  have hrep' := fun q => congrArg (Multiset.count q) hrep.val_add_val_eq
  simp only [Multiset.count_add, Multiset.count_eq_of_nodup (Finset.nodup _), Finset.mem_val,
    toRectangleDecomposition_first_toGridRectangle,
    toRectangleDecomposition_second_toGridRectangle] at hrep'
  refine Multiset.ext.mpr fun p => ?_
  simp only [Multiset.count_add, Multiset.count_eq_of_nodup (Finset.nodup _), Finset.mem_val]
  obtain ⟨c, t⟩ := p
  by_cases hca : c = a
  · subst hca
    have h := hrep' (c, t)
    have h₁ := Grid.ite_mem_cIco_eq_add_add D'.pentagon.turn_mem_cIco_bottom_top t
    have h₂ := Grid.ite_mem_cIco_eq_add_add D.pentagon.turn_mem_cIco_bottom_top t
    simp only [GridPentagonBetween.mk_mem_coveredSquares_left_column,
      GridPentagonBetween.mk_mem_toGridRectangle_coveredSquares_left_column] at h ⊢
    rw [hbottom] at h h₁
    omega
  by_cases hcb : c = finRotate n a
  · subst hcb
    have h := hrep' (finRotate n a, t)
    simp only [GridPentagonBetween.mk_mem_coveredSquares_right_column,
      GridPentagonBetween.mk_notMem_toGridRectangle_coveredSquares_right_column, ↓reduceIte,
      add_zero, hbottom] at h ⊢
    omega
  · have h := hrep' (c, t)
    simp only [D'.pentagon.mem_coveredSquares_iff_of_ne (p := (c, t)) hca hcb,
      D.pentagon.mem_coveredSquares_iff_of_ne (p := (c, t)) hca hcb]
    omega

end GridRectanglePentagonDecomposition

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

local notation "b" => finRotate n C.column

/-- The rectangle--pentagon decompositions counted by the coefficient of the pentagon map after
the original differential. -/
noncomputable def rectanglePentagonDecompositions (x z : GridState n) :
    Finset (GridRectanglePentagonDecomposition C.column C.turnRow x z) :=
  GridRectanglePentagonDecomposition.decompositionsOf G.unblockedRectangles
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
  GridPentagonRectangleDecomposition.decompositionsOf (fun u v => G.pentagons C u v)
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
empty and no square of its composite domain, the rectangle of the commuted diagram being read in the
original diagram, carries an `X`-marking. -/
theorem mem_pentagonRectangleDecompositions_of_forall_notMem_XSet {x z : GridState n}
    {D : GridPentagonRectangleDecomposition C.column C.turnRow x z}
    (hpentagon : D.pentagon.IsEmpty) (hrectangle : D.rectangle.IsEmpty)
    (hX : ∀ p ∈ D.pentagon.coveredSquares.val +
        (D.rectangle.toGridRectangle.coveredSquares.map
          ((Equiv.swap C.column b).prodCongr (Equiv.refl (Fin n))).toEmbedding).val,
      p ∉ G.XSet) :
    D ∈ G.pentagonRectangleDecompositions C x z := by
  rw [mem_pentagonRectangleDecompositions, mem_pentagons,
    (G.swapColumns C.column b).mem_unblockedRectangles, ← G.disjoint_map_swapColumns_XSet_iff]
  exact ⟨⟨hpentagon, Finset.disjoint_left.mpr fun p hp => hX p (Multiset.mem_add.mpr (Or.inl hp))⟩,
    hrectangle, Finset.disjoint_left.mpr fun p hp => hX p (Multiset.mem_add.mpr (Or.inr hp))⟩

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
  refine G.mem_pentagonRectangleDecompositions_of_forall_notMem_XSet C hpentagon hrectangle
    fun p hp hpX => ?_
  rw [h] at hp
  rcases Multiset.mem_add.mp hp with hp' | hp'
  · exact Finset.disjoint_left.mp hD.1.2 hp' hpX
  · exact Finset.disjoint_left.mp hD.2.2 hp' hpX

/-- A pentagon followed by a rectangle of the commuted diagram is counted when its two domains are
empty and its composite domain covers, with multiplicity, the squares of another counted pentagon
followed by a rectangle, both rectangles being read in the original diagram: every square it
covers then avoids the `X`-markings. -/
theorem mem_pentagonRectangleDecompositions_of_val_add_val_eq_pentagonRectangle
    {x z : GridState n} {E : GridPentagonRectangleDecomposition C.column C.turnRow x z}
    (hE : E ∈ G.pentagonRectangleDecompositions C x z)
    {D : GridPentagonRectangleDecomposition C.column C.turnRow x z}
    (hpentagon : D.pentagon.IsEmpty) (hrectangle : D.rectangle.IsEmpty)
    (h : D.pentagon.coveredSquares.val +
        (D.rectangle.toGridRectangle.coveredSquares.map
          ((Equiv.swap C.column b).prodCongr (Equiv.refl (Fin n))).toEmbedding).val =
      E.pentagon.coveredSquares.val +
        (E.rectangle.toGridRectangle.coveredSquares.map
          ((Equiv.swap C.column b).prodCongr (Equiv.refl (Fin n))).toEmbedding).val) :
    D ∈ G.pentagonRectangleDecompositions C x z := by
  rw [mem_pentagonRectangleDecompositions, mem_pentagons,
    (G.swapColumns C.column b).mem_unblockedRectangles,
    ← G.disjoint_map_swapColumns_XSet_iff] at hE
  refine G.mem_pentagonRectangleDecompositions_of_forall_notMem_XSet C hpentagon hrectangle
    fun p hp hpX => ?_
  rw [h] at hp
  rcases Multiset.mem_add.mp hp with hp' | hp'
  · exact Finset.disjoint_left.mp hE.1.2 hp' hpX
  · exact Finset.disjoint_left.mp hE.2.2 hp' hpX

/-- A rectangle followed by a pentagon is counted when its two domains are empty and its composite
domain covers, with multiplicity, the squares of a counted rectangle followed by a pentagon: every
square it covers then avoids the `X`-markings. -/
theorem mem_rectanglePentagonDecompositions_of_val_add_val_eq {x z : GridState n}
    {D : GridRectanglePentagonDecomposition C.column C.turnRow x z}
    (hD : D ∈ G.rectanglePentagonDecompositions C x z)
    {D' : GridRectanglePentagonDecomposition C.column C.turnRow x z}
    (hrectangle : D'.rectangle.IsEmpty) (hpentagon : D'.pentagon.IsEmpty)
    (h : D'.rectangle.toGridRectangle.coveredSquares.val + D'.pentagon.coveredSquares.val =
      D.rectangle.toGridRectangle.coveredSquares.val + D.pentagon.coveredSquares.val) :
    D' ∈ G.rectanglePentagonDecompositions C x z := by
  rw [mem_rectanglePentagonDecompositions, mem_unblockedRectangles, mem_pentagons] at hD ⊢
  -- A square of the new domain is a square of the original domain, which avoids `X`.
  have hX (p : Fin n × Fin n) (hp : p ∈ D'.rectangle.toGridRectangle.coveredSquares.val +
      D'.pentagon.coveredSquares.val) : p ∉ G.XSet := fun hpX => by
    rw [h] at hp
    rcases Multiset.mem_add.mp hp with hp' | hp'
    · exact Finset.disjoint_left.mp hD.1.2 hp' hpX
    · exact Finset.disjoint_left.mp hD.2.2 hp' hpX
  exact ⟨⟨hrectangle, Finset.disjoint_left.mpr fun p hp => hX p (Multiset.mem_add.mpr (Or.inl hp))⟩,
    hpentagon, Finset.disjoint_left.mpr fun p hp => hX p (Multiset.mem_add.mpr (Or.inr hp))⟩

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
  exact (GridRectanglePentagonDecomposition.sum_decompositionsOf
    G.unblockedRectangles (fun u v => G.pentagons C u v) x z
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
  exact (GridPentagonRectangleDecomposition.sum_decompositionsOf
    (fun u v => G.pentagons C u v)
    (G.swapColumns C.column b).unblockedRectangles x z
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
