/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Basic
public import TauCeti.KnotTheory.Grid.TwoStepDecomposition
public import TauCeti.KnotTheory.Grid.Differential.Square.Decomposition

/-!
# Composite domains in the grid-commutation homotopy equation

The homotopy equation for a column commutation compares three kinds of two-step domain. On its
left are a commutation hexagon followed by a rectangle and a rectangle followed by a commutation
hexagon. On its right are two commutation pentagons, the second for the reverse commutation. Each
commutation polygon may turn on either side of the replaced grid line.

This file packages those alternatives and rewrites the matrix-coefficient equation as sums over
finite families of composite domains. In this form every summand records the actual polygons it
counts, rather than only their intermediate grid state. This is the input for the geometric
pairing of juxtaposed domains in the proof of commutation invariance.

The two kinds of hexagon and pentagon are represented by sum types. This retains the distinction
between the two turn sides while avoiding four parallel decomposition types. All three composite
domain families specialize the generic two-step decomposition `TauCeti.GridTwoStepDecomposition`,
whose counted finite families have membership characterizations.

## Main results

* `TauCeti.GridDiagram.sum_commutationHexagonCoefficient_mul_unblockedCoefficient` and
  `TauCeti.GridDiagram.sum_unblockedCoefficient_mul_commutationHexagonCoefficient` rewrite the
  two rectangle--hexagon matrix products as composite-domain sums.
* `TauCeti.GridDiagram.sum_rename_commutationPentagonCoefficient_mul_commutationPentagonCoefficient`
  rewrites the round-trip commutation coefficient as a sum over pairs of pentagons.
* `TauCeti.GridDiagram.unblockedDifferential_commutationHomotopy_add_eq_iff_decompositions`
  states the homotopy equation entirely in terms of the three finite domain families.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti

/-- A commutation hexagon for column `a`, turn row `s` and opposite turn row `s'` is either a
hexagon turning on its terminal side or one turning on its initial side.

The two row parameters play opposite roles in the two cases: the terminal-side hexagon
`GridHexagonBetween a s' s` cuts away the bigon from `s'` up to `s`, while the initial-side hexagon
`GridInitialHexagonBetween a s s'` cuts away the bigon from `s` up to `s'`. -/
abbrev GridCommutationHexagonBetween {n : ℕ} (a s s' : Fin n) (x y : GridState n) :=
  GridHexagonBetween a s' s x y ⊕ GridInitialHexagonBetween a s s' x y

namespace GridCommutationHexagonBetween

variable {n : ℕ} {a s s' : Fin n} {x y : GridState n}

/-- Forget the two turns of a commutation hexagon, retaining its oriented rectangle. -/
def toGridRectangleBetween (P : GridCommutationHexagonBetween a s s' x y) :
    GridRectangleBetween x y :=
  P.elim GridHexagonBetween.toGridRectangleBetween
    GridInitialHexagonBetween.toGridRectangleBetween

/-- The toGridRectangleBetween accessor on a terminal-side hexagon. -/
@[simp]
theorem toGridRectangleBetween_inl (P : GridHexagonBetween a s' s x y) :
    toGridRectangleBetween (Sum.inl P) = P.toGridRectangleBetween := (rfl)

/-- The toGridRectangleBetween accessor on a initial-side hexagon. -/
@[simp]
theorem toGridRectangleBetween_inr (P : GridInitialHexagonBetween a s s' x y) :
    toGridRectangleBetween (Sum.inr P) = P.toGridRectangleBetween := (rfl)

/-- The underlying rectangle determines a commutation hexagon, including its turn side. -/
theorem toGridRectangleBetween_injective :
    Function.Injective (toGridRectangleBetween (a := a) (s := s) (s' := s')
      (x := x) (y := y)) := by
  intro P Q h
  cases P with
  | inl P =>
    cases Q with
    | inl Q => exact congrArg Sum.inl (Subsingleton.elim P Q)
    | inr Q =>
      have hl := congrArg GridRectangleBetween.left h
      exact False.elim (P.left_ne (hl.trans Q.left_eq))
  | inr P =>
    cases Q with
    | inl Q =>
      have hl := congrArg GridRectangleBetween.left h
      exact False.elim (Q.left_ne (hl.symm.trans P.left_eq))
    | inr Q => exact congrArg Sum.inr (Subsingleton.elim P Q)

/-- The marking squares covered by a commutation hexagon of either turn-side kind. -/
noncomputable def coveredSquares (P : GridCommutationHexagonBetween a s s' x y) :
    Finset (Fin n × Fin n) :=
  P.elim GridHexagonBetween.coveredSquares GridInitialHexagonBetween.coveredSquares

/-- The coveredSquares accessor on a terminal-side hexagon. -/
@[simp]
theorem coveredSquares_inl (P : GridHexagonBetween a s' s x y) :
    coveredSquares (Sum.inl P) = P.coveredSquares := (rfl)

/-- The coveredSquares accessor on a initial-side hexagon. -/
@[simp]
theorem coveredSquares_inr (P : GridInitialHexagonBetween a s s' x y) :
    coveredSquares (Sum.inr P) = P.coveredSquares := (rfl)

/-- Transfer a commutation hexagon along an equality of underlying toroidal rectangles,
preserving the turn-side kind. -/
def ofToGridRectangleEq {u v : GridState n} (r : GridRectangleBetween u v)
    (P : GridCommutationHexagonBetween a s s' x y)
    (h : r.toGridRectangle = P.toGridRectangleBetween.toGridRectangle) :
    GridCommutationHexagonBetween a s s' u v :=
  match P with
  | Sum.inl P => Sum.inl (GridHexagonBetween.ofToGridRectangleEq r P h)
  | Sum.inr P => Sum.inr (GridInitialHexagonBetween.ofToGridRectangleEq r P h)

/-- Forgetting a transferred commutation hexagon returns the supplied rectangle. -/
@[simp]
theorem ofToGridRectangleEq_toGridRectangleBetween {u v : GridState n}
    (r : GridRectangleBetween u v) (P : GridCommutationHexagonBetween a s s' x y)
    (h : r.toGridRectangle = P.toGridRectangleBetween.toGridRectangle) :
    (ofToGridRectangleEq r P h).toGridRectangleBetween = r := by
  cases P with
  | inl P => exact GridHexagonBetween.ofToGridRectangleEq_toGridRectangleBetween r P h
  | inr P => exact GridInitialHexagonBetween.ofToGridRectangleEq_toGridRectangleBetween r P h

/-- Transferring a commutation hexagon preserves the marking squares it covers. -/
@[simp]
theorem ofToGridRectangleEq_coveredSquares {u v : GridState n}
    (r : GridRectangleBetween u v) (P : GridCommutationHexagonBetween a s s' x y)
    (h : r.toGridRectangle = P.toGridRectangleBetween.toGridRectangle) :
    (ofToGridRectangleEq r P h).coveredSquares = P.coveredSquares := by
  cases P with
  | inl P =>
    exact GridHexagonBetween.coveredSquares_eq_of_toGridRectangle_eq _ _
      ((congrArg GridRectangleBetween.toGridRectangle
        (GridHexagonBetween.ofToGridRectangleEq_toGridRectangleBetween r P h)).trans h)
  | inr P =>
    exact GridInitialHexagonBetween.coveredSquares_eq_of_toGridRectangle_eq _ _
      ((congrArg GridRectangleBetween.toGridRectangle
        (GridInitialHexagonBetween.ofToGridRectangleEq_toGridRectangleBetween r P h)).trans h)

end GridCommutationHexagonBetween

/-- A commutation pentagon is either a pentagon turning on its terminal side or one turning on its
initial side. -/
abbrev GridCommutationPentagonBetween {n : ℕ} (a s : Fin n) (x y : GridState n) :=
  GridPentagonBetween a s x y ⊕ GridInitialPentagonBetween a s x y

/-- A two-step domain consisting of a commutation hexagon followed by a rectangle. -/
abbrev GridHexagonRectangleDecomposition {n : ℕ} (a s s' : Fin n)
    (x z : GridState n) :=
  GridTwoStepDecomposition (GridCommutationHexagonBetween a s s') GridRectangleBetween x z

namespace GridHexagonRectangleDecomposition

/-- The commutation hexagon in a hexagon--rectangle decomposition. -/
abbrev hexagon {n : ℕ} {a s s' : Fin n} {x z : GridState n}
    (D : GridHexagonRectangleDecomposition a s s' x z) := D.first

/-- The rectangle in a hexagon--rectangle decomposition. -/
abbrev rectangle {n : ℕ} {a s s' : Fin n} {x z : GridState n}
    (D : GridHexagonRectangleDecomposition a s s' x z) := D.second

variable {n : ℕ} {a s s' : Fin n} {x z : GridState n}

/-- Forget the turns of the hexagon in a hexagon--rectangle domain. -/
abbrev toRectangleDecomposition (D : GridHexagonRectangleDecomposition a s s' x z) :
    GridRectangleDecomposition x z :=
  ⟨D.middle, D.first.toGridRectangleBetween, D.second⟩

/-- Forgetting the hexagon turns is injective on two-step domains. -/
theorem toRectangleDecomposition_injective :
    Function.Injective (toRectangleDecomposition (a := a) (s := s) (s' := s')
      (x := x) (z := z)) := by
  rintro ⟨m, P, r⟩ ⟨m', Q, t⟩ h
  have hm : m = m' := congrArg GridTwoStepDecomposition.middle h
  subst m'
  have hp : P.toGridRectangleBetween = Q.toGridRectangleBetween := by injection h
  have hr : r = t := by injection h
  rw [GridCommutationHexagonBetween.toGridRectangleBetween_injective hp, hr]

end GridHexagonRectangleDecomposition

/-- A two-step domain consisting of a rectangle followed by a commutation hexagon. -/
abbrev GridRectangleHexagonDecomposition {n : ℕ} (a s s' : Fin n)
    (x z : GridState n) :=
  GridTwoStepDecomposition GridRectangleBetween (GridCommutationHexagonBetween a s s') x z

namespace GridRectangleHexagonDecomposition

/-- The rectangle in a rectangle--hexagon decomposition. -/
abbrev rectangle {n : ℕ} {a s s' : Fin n} {x z : GridState n}
    (D : GridRectangleHexagonDecomposition a s s' x z) := D.first

/-- The commutation hexagon in a rectangle--hexagon decomposition. -/
abbrev hexagon {n : ℕ} {a s s' : Fin n} {x z : GridState n}
    (D : GridRectangleHexagonDecomposition a s s' x z) := D.second

variable {n : ℕ} {a s s' : Fin n} {x z : GridState n}

/-- Forget the turns of the hexagon in a rectangle--hexagon domain. -/
abbrev toRectangleDecomposition (D : GridRectangleHexagonDecomposition a s s' x z) :
    GridRectangleDecomposition x z :=
  ⟨D.middle, D.first, D.second.toGridRectangleBetween⟩

/-- Forgetting the hexagon turns is injective on two-step domains. -/
theorem toRectangleDecomposition_injective :
    Function.Injective (toRectangleDecomposition (a := a) (s := s) (s' := s')
      (x := x) (z := z)) := by
  rintro ⟨m, r, P⟩ ⟨m', t, Q⟩ h
  have hm : m = m' := congrArg GridTwoStepDecomposition.middle h
  subst m'
  have hr : r = t := by injection h
  have hp : P.toGridRectangleBetween = Q.toGridRectangleBetween := by injection h
  rw [hr, GridCommutationHexagonBetween.toGridRectangleBetween_injective hp]

end GridRectangleHexagonDecomposition

/-- A two-step domain consisting of a commutation pentagon followed by a pentagon for the reverse
commutation. -/
abbrev GridPentagonPairDecomposition {n : ℕ} (a s b t : Fin n)
    (x z : GridState n) :=
  GridTwoStepDecomposition (GridCommutationPentagonBetween a s)
    (GridCommutationPentagonBetween b t) x z

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

local notation "b" => finRotate n C.column

/-- The counted commutation hexagons of either turn-side kind. -/
noncomputable def commutationHexagons (x y : GridState n) :
    Finset (GridCommutationHexagonBetween C.column C.turnRow C.oppositeTurnRow x y) :=
  (G.hexagons C x y).disjSum (G.initialHexagons C x y)

/-- A commutation hexagon is counted exactly when its underlying rectangle is empty and
its marking squares avoid every `X`-marking. -/
@[simp]
theorem mem_commutationHexagons {x y : GridState n}
    (P : GridCommutationHexagonBetween C.column C.turnRow C.oppositeTurnRow x y) :
    P ∈ G.commutationHexagons C x y ↔
      P.toGridRectangleBetween.IsEmpty ∧ Disjoint P.coveredSquares G.XSet := by
  cases P <;> simp [commutationHexagons,
    GridCommutationHexagonBetween.toGridRectangleBetween,
    GridCommutationHexagonBetween.coveredSquares]

/-- The counted commutation pentagons of either turn-side kind. -/
noncomputable def commutationPentagons (x y : GridState n) :
    Finset (GridCommutationPentagonBetween C.column C.turnRow x y) :=
  (G.pentagons C x y).disjSum (G.initialPentagons C x y)

/-- A terminal-side commutation pentagon is counted exactly when it is a counted pentagon. -/
@[simp]
theorem inl_mem_commutationPentagons {x y : GridState n}
    (P : GridPentagonBetween C.column C.turnRow x y) :
    Sum.inl P ∈ G.commutationPentagons C x y ↔ P ∈ G.pentagons C x y :=
  Finset.inl_mem_disjSum

/-- An initial-side commutation pentagon is counted exactly when it is a counted initial-side
pentagon. -/
@[simp]
theorem inr_mem_commutationPentagons {x y : GridState n}
    (P : GridInitialPentagonBetween C.column C.turnRow x y) :
    Sum.inr P ∈ G.commutationPentagons C x y ↔ P ∈ G.initialPentagons C x y :=
  Finset.inr_mem_disjSum

variable (R : Type*) [CommSemiring R]

/-- The weight of a commutation hexagon of either kind. -/
noncomputable def commutationHexagonWeight {x y : GridState n}
    (P : GridCommutationHexagonBetween C.column C.turnRow C.oppositeTurnRow x y) :
    MvPolynomial (Fin n) R :=
  P.elim (G.hexagonWeight R) (G.initialHexagonWeight R)

/-- The weight of a terminal-side commutation hexagon. -/
@[simp]
theorem commutationHexagonWeight_inl {x y : GridState n}
    (P : GridHexagonBetween C.column C.oppositeTurnRow C.turnRow x y) :
    G.commutationHexagonWeight C R (Sum.inl P) = G.hexagonWeight R P := (rfl)

/-- The weight of an initial-side commutation hexagon. -/
@[simp]
theorem commutationHexagonWeight_inr {x y : GridState n}
    (P : GridInitialHexagonBetween C.column C.turnRow C.oppositeTurnRow x y) :
    G.commutationHexagonWeight C R (Sum.inr P) = G.initialHexagonWeight R P := (rfl)

/-- The weight of a commutation hexagon is the product of the per-square `O`-weights. -/
theorem commutationHexagonWeight_eq_prod_coveredSquares {x y : GridState n}
    (P : GridCommutationHexagonBetween C.column C.turnRow C.oppositeTurnRow x y) :
    G.commutationHexagonWeight C R P =
      ∏ p ∈ P.coveredSquares, if p ∈ G.OSet then MvPolynomial.X p.1 else 1 := by
  cases P with
  | inl P => exact G.hexagonWeight_eq_prod_coveredSquares R P
  | inr P => exact G.initialHexagonWeight_eq_prod_coveredSquares R P

/-- The weight of a commutation pentagon of either kind. -/
noncomputable def commutationPentagonWeight {x y : GridState n}
    (P : GridCommutationPentagonBetween C.column C.turnRow x y) :
    MvPolynomial (Fin n) R :=
  P.elim (G.pentagonWeight R C) (G.initialPentagonWeight R C)

/-- The weight of a terminal-side commutation pentagon. -/
@[simp]
theorem commutationPentagonWeight_inl {x y : GridState n}
    (P : GridPentagonBetween C.column C.turnRow x y) :
    G.commutationPentagonWeight C R (Sum.inl P) = G.pentagonWeight R C P := (rfl)

/-- The weight of an initial-side commutation pentagon. -/
@[simp]
theorem commutationPentagonWeight_inr {x y : GridState n}
    (P : GridInitialPentagonBetween C.column C.turnRow x y) :
    G.commutationPentagonWeight C R (Sum.inr P) = G.initialPentagonWeight R C P := (rfl)

/-- The hexagon--rectangle decompositions counted in the coefficient of the differential after
the commutation homotopy. -/
noncomputable def hexagonRectangleDecompositions (x z : GridState n) :
    Finset (GridHexagonRectangleDecomposition C.column C.turnRow C.oppositeTurnRow x z) :=
  GridTwoStepDecomposition.decompositionsOf (G.commutationHexagons C)
    G.unblockedRectangles x z

/-- Membership in the counted hexagon--rectangle family is countedness of both domains. -/
@[simp]
theorem mem_hexagonRectangleDecompositions {x z : GridState n}
    (D : GridHexagonRectangleDecomposition C.column C.turnRow C.oppositeTurnRow x z) :
    D ∈ G.hexagonRectangleDecompositions C x z ↔
      D.hexagon ∈ G.commutationHexagons C x D.middle ∧
        D.rectangle ∈ G.unblockedRectangles D.middle z := by
  classical
  simp [hexagonRectangleDecompositions]

/-- The rectangle--hexagon decompositions counted in the coefficient of the commutation homotopy
after the differential. -/
noncomputable def rectangleHexagonDecompositions (x z : GridState n) :
    Finset (GridRectangleHexagonDecomposition C.column C.turnRow C.oppositeTurnRow x z) :=
  GridTwoStepDecomposition.decompositionsOf G.unblockedRectangles
    (G.commutationHexagons C) x z

/-- Membership in the counted rectangle--hexagon family is countedness of both domains. -/
@[simp]
theorem mem_rectangleHexagonDecompositions {x z : GridState n}
    (D : GridRectangleHexagonDecomposition C.column C.turnRow C.oppositeTurnRow x z) :
    D ∈ G.rectangleHexagonDecompositions C x z ↔
      D.rectangle ∈ G.unblockedRectangles x D.middle ∧
        D.hexagon ∈ G.commutationHexagons C D.middle z := by
  classical
  simp [rectangleHexagonDecompositions]

/-- The pairs of forward and reverse pentagons counted in the round-trip commutation map. -/
noncomputable def pentagonPairDecompositions (x z : GridState n) :
    Finset (GridPentagonPairDecomposition C.column C.turnRow C.reverse.column
      C.reverse.turnRow x z) :=
  GridTwoStepDecomposition.decompositionsOf (G.commutationPentagons C)
    ((G.swapColumns C.column b).commutationPentagons C.reverse) x z

/-- Membership in the counted pentagon-pair family is countedness of the forward and reverse
pentagons. -/
@[simp]
theorem mem_pentagonPairDecompositions {x z : GridState n}
    (D : GridPentagonPairDecomposition C.column C.turnRow C.reverse.column
      C.reverse.turnRow x z) :
    D ∈ G.pentagonPairDecompositions C x z ↔
      D.first ∈ G.commutationPentagons C x D.middle ∧
        D.second ∈ (G.swapColumns C.column b).commutationPentagons C.reverse D.middle z := by
  classical
  simp [pentagonPairDecompositions]

/-- The weight of a counted hexagon followed by a rectangle. -/
noncomputable def hexagonRectangleWeight {x z : GridState n}
    (D : GridHexagonRectangleDecomposition C.column C.turnRow C.oppositeTurnRow x z) :
    MvPolynomial (Fin n) R :=
  G.commutationHexagonWeight C R D.hexagon * G.OMonomial R D.rectangle.toGridRectangle

/-- The weight of a hexagon--rectangle decomposition is the product of the two domain weights. -/
theorem hexagonRectangleWeight_def {x z : GridState n}
    (D : GridHexagonRectangleDecomposition C.column C.turnRow C.oppositeTurnRow x z) :
    G.hexagonRectangleWeight C R D =
      G.commutationHexagonWeight C R D.hexagon *
        G.OMonomial R D.rectangle.toGridRectangle := (rfl)

/-- The weight of a counted rectangle followed by a hexagon. -/
noncomputable def rectangleHexagonWeight {x z : GridState n}
    (D : GridRectangleHexagonDecomposition C.column C.turnRow C.oppositeTurnRow x z) :
    MvPolynomial (Fin n) R :=
  G.OMonomial R D.rectangle.toGridRectangle * G.commutationHexagonWeight C R D.hexagon

/-- The weight of a rectangle--hexagon decomposition is the product of the two domain weights. -/
theorem rectangleHexagonWeight_def {x z : GridState n}
    (D : GridRectangleHexagonDecomposition C.column C.turnRow C.oppositeTurnRow x z) :
    G.rectangleHexagonWeight C R D =
      G.OMonomial R D.rectangle.toGridRectangle *
        G.commutationHexagonWeight C R D.hexagon := (rfl)

/-- The weight of a forward pentagon followed by a reverse pentagon. The first factor is renamed
because the forward commutation map is semilinear. -/
noncomputable def pentagonPairWeight {x z : GridState n}
    (D : GridPentagonPairDecomposition C.column C.turnRow C.reverse.column
      C.reverse.turnRow x z) :
    MvPolynomial (Fin n) R :=
  MvPolynomial.rename (Equiv.swap C.column b) (G.commutationPentagonWeight C R D.first) *
    (G.swapColumns C.column b).commutationPentagonWeight C.reverse R D.second

/-- The weight of a pentagon pair is the product of the renamed forward weight and the reverse
weight. -/
theorem pentagonPairWeight_def {x z : GridState n}
    (D : GridPentagonPairDecomposition C.column C.turnRow C.reverse.column
      C.reverse.turnRow x z) :
    G.pentagonPairWeight C R D =
      MvPolynomial.rename (Equiv.swap C.column b) (G.commutationPentagonWeight C R D.first) *
        (G.swapColumns C.column b).commutationPentagonWeight C.reverse R D.second := (rfl)

/-- The sum of the two kinds of hexagon coefficients is the sum of their combined weights. -/
theorem commutationHexagonCoefficient_eq_sum_weight (x y : GridState n) :
    G.commutationHexagonCoefficient R C x y =
      ∑ P ∈ G.commutationHexagons C x y, G.commutationHexagonWeight C R P := by
  rw [G.commutationHexagonCoefficient_def R C, G.hexagonCoefficient_def R C x y,
    G.initialHexagonCoefficient_def R C x y, commutationHexagons, Finset.sum_disjSum]
  simp only [commutationHexagonWeight_inl, commutationHexagonWeight_inr]

/-- The sum of the two kinds of pentagon coefficients is the sum of their combined weights. -/
theorem commutationPentagonCoefficient_eq_sum_weight (x y : GridState n) :
    G.commutationPentagonCoefficient R C x y =
      ∑ P ∈ G.commutationPentagons C x y, G.commutationPentagonWeight C R P := by
  rw [G.commutationPentagonCoefficient_def R C, G.pentagonCoefficient_def R C x y,
    G.initialPentagonCoefficient_def R C x y, commutationPentagons, Finset.sum_disjSum]
  simp only [commutationPentagonWeight_inl, commutationPentagonWeight_inr]

/-- The hexagon--rectangle matrix product is the sum of the weights of the counted composite
domains. -/
theorem sum_commutationHexagonCoefficient_mul_unblockedCoefficient (x z : GridState n) :
    ∑ y : GridState n,
        G.commutationHexagonCoefficient R C x y * G.unblockedCoefficient R y z =
      ∑ D ∈ G.hexagonRectangleDecompositions C x z, G.hexagonRectangleWeight C R D := by
  simp_rw [G.commutationHexagonCoefficient_eq_sum_weight C R,
    G.unblockedCoefficient_def R, Finset.sum_mul_sum]
  exact (GridTwoStepDecomposition.sum_decompositionsOf
    (G.commutationHexagons C) G.unblockedRectangles
    (fun _ P r => G.commutationHexagonWeight C R P * G.OMonomial R r.toGridRectangle)).symm

/-- The rectangle--hexagon matrix product is the sum of the weights of the counted composite
domains. -/
theorem sum_unblockedCoefficient_mul_commutationHexagonCoefficient (x z : GridState n) :
    ∑ y : GridState n, G.unblockedCoefficient R x y *
        G.commutationHexagonCoefficient R C y z =
      ∑ D ∈ G.rectangleHexagonDecompositions C x z, G.rectangleHexagonWeight C R D := by
  simp_rw [G.unblockedCoefficient_def R, G.commutationHexagonCoefficient_eq_sum_weight C R,
    Finset.sum_mul_sum]
  exact (GridTwoStepDecomposition.sum_decompositionsOf G.unblockedRectangles
    (G.commutationHexagons C)
    (fun _ r P => G.OMonomial R r.toGridRectangle * G.commutationHexagonWeight C R P)).symm

/-- The forward--reverse pentagon matrix product is the sum of the weights of the counted
pentagon pairs. -/
theorem sum_rename_commutationPentagonCoefficient_mul_commutationPentagonCoefficient
    (x z : GridState n) :
    ∑ y : GridState n,
        MvPolynomial.rename (Equiv.swap C.column b)
            (G.commutationPentagonCoefficient R C x y) *
          (G.swapColumns C.column b).commutationPentagonCoefficient R C.reverse y z =
      ∑ D ∈ G.pentagonPairDecompositions C x z, G.pentagonPairWeight C R D := by
  simp_rw [G.commutationPentagonCoefficient_eq_sum_weight C R,
    (G.swapColumns C.column b).commutationPentagonCoefficient_eq_sum_weight C.reverse R,
    map_sum, Finset.sum_mul_sum]
  exact (GridTwoStepDecomposition.sum_decompositionsOf (G.commutationPentagons C)
    ((G.swapColumns C.column b).commutationPentagons C.reverse)
    (fun _ P Q => MvPolynomial.rename (Equiv.swap C.column b)
      (G.commutationPentagonWeight C R P) *
        (G.swapColumns C.column b).commutationPentagonWeight C.reverse R Q)).symm

/-- The commutation homotopy equation holds exactly when the three finite composite-domain sums
satisfy the coefficient identity for every source and target state. -/
theorem unblockedDifferential_commutationHomotopy_add_eq_iff_decompositions :
    (∀ c : GridChainMinus R n,
      G.unblockedDifferential R (G.commutationHomotopy R C c) +
          G.commutationHomotopy R C (G.unblockedDifferential R c) =
        c + (G.swapColumns C.column b).commutationMap R C.reverse (G.commutationMap R C c)) ↔
      ∀ x z : GridState n,
        (∑ D ∈ G.hexagonRectangleDecompositions C x z, G.hexagonRectangleWeight C R D) +
            ∑ D ∈ G.rectangleHexagonDecompositions C x z,
              G.rectangleHexagonWeight C R D =
          (if x = z then 1 else 0) +
            ∑ D ∈ G.pentagonPairDecompositions C x z, G.pentagonPairWeight C R D := by
  rw [G.unblockedDifferential_commutationHomotopy_add_eq_iff C R]
  simp_rw [Finset.sum_add_distrib,
    G.sum_commutationHexagonCoefficient_mul_unblockedCoefficient C R,
    G.sum_unblockedCoefficient_mul_commutationHexagonCoefficient C R,
    G.sum_rename_commutationPentagonCoefficient_mul_commutationPentagonCoefficient C R]

end GridDiagram

end TauCeti
