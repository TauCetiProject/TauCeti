/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import TauCeti.KnotTheory.Grid.Commutation.Pentagon
public import TauCeti.KnotTheory.Grid.Differential.Square.Recut.Mixed

/-!
# Rectangle--pentagon decompositions for grid commutation

The chain-map equation for the pentagon map of a column commutation compares two kinds of
two-step domain. In one order, a rectangle in the original diagram is followed by a pentagon;
in the other, a pentagon is followed by a rectangle in the commuted diagram. This file packages
the two kinds of decomposition and rewrites the two matrix products in the chain-map equation as
sums over them.

For a validated column commutation `C` of `G`, write `G'` for the diagram obtained by swapping
the columns of `C`. The coefficient of `Phi (partial x)` at `z` is the sum over
`GridRectanglePentagonDecomposition C.column C.turnRow x z`; its weight is the rectangle weight,
renamed into the coefficient variables of `G'`, times the pentagon weight. The coefficient of
`partial' (Phi x)` is the sum over `GridPentagonRectangleDecomposition C.column C.turnRow x z`;
its weight is the pentagon weight times the rectangle weight in `G'`.

The remaining geometric step in commutation invariance is to match these two finite sets by
repartitioning each composite domain. Keeping the counting identities here separate from that
geometric pairing makes the exact target of the juxtaposition argument explicit.

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
* `TauCeti.GridRectanglePentagonDecomposition.isEmpty_toRectangleDecomposition_first` and
  `TauCeti.GridPentagonRectangleDecomposition.turn_mem_toRectangleDecomposition_second` transport
  emptiness and the pentagon turn point to the underlying rectangles.

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

/-- Emptiness of the pentagon is preserved when forgetting its turn point. -/
theorem isEmpty_toRectangleDecomposition_first
    (D : GridPentagonRectangleDecomposition a s x z) (h : D.pentagon.IsEmpty) :
    D.toRectangleDecomposition.first.IsEmpty := by
  cases D with
  | mk middle pentagon rectangle =>
      unfold toRectangleDecomposition
      exact h

/-- Emptiness of the rectangle is preserved when forgetting the pentagon turn point. -/
theorem isEmpty_toRectangleDecomposition_second
    (D : GridPentagonRectangleDecomposition a s x z) (h : D.rectangle.IsEmpty) :
    D.toRectangleDecomposition.second.IsEmpty := by
  cases D with
  | mk middle pentagon rectangle =>
      unfold toRectangleDecomposition
      exact h

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

/-- Emptiness of the rectangle is preserved when forgetting the pentagon turn point. -/
theorem isEmpty_toRectangleDecomposition_first (D : GridRectanglePentagonDecomposition a s x z)
    (h : D.rectangle.IsEmpty) : D.toRectangleDecomposition.first.IsEmpty := by
  cases D with
  | mk middle rectangle pentagon =>
      unfold toRectangleDecomposition
      exact h

/-- Emptiness of the pentagon's underlying rectangle is preserved when forgetting its turn row. -/
theorem isEmpty_toRectangleDecomposition_second
    (D : GridRectanglePentagonDecomposition a s x z) (h : D.pentagon.IsEmpty) :
    D.toRectangleDecomposition.second.IsEmpty := by
  cases D with
  | mk middle rectangle pentagon =>
      unfold toRectangleDecomposition
      exact h

/-- The pentagon's turn row lies between the sides of the second forgotten rectangle. -/
theorem turn_mem_toRectangleDecomposition_second
    (D : GridRectanglePentagonDecomposition a s x z) :
    s ∈ Grid.cIco D.toRectangleDecomposition.second.bottom
      D.toRectangleDecomposition.second.top := by
  cases D with
  | mk middle rectangle pentagon =>
      unfold toRectangleDecomposition
      exact pentagon.turn_mem

/-- The pentagon's turn row lies between the sides of the first forgotten rectangle. -/
theorem turn_mem_toRectangleDecomposition_first
    (D : GridPentagonRectangleDecomposition a s x z) :
    s ∈ Grid.cIco D.toRectangleDecomposition.first.bottom
      D.toRectangleDecomposition.first.top := by
  cases D with
  | mk middle pentagon rectangle =>
      unfold GridPentagonRectangleDecomposition.toRectangleDecomposition
      exact pentagon.turn_mem

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
