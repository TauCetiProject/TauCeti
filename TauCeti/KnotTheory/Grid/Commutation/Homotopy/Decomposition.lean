/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Basic
public import TauCeti.KnotTheory.Grid.TwoStepDecomposition

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

/-- A commutation hexagon is counted exactly when the corresponding hexagon of its kind is
counted. -/
@[simp]
theorem mem_commutationHexagons {x y : GridState n}
    (P : GridCommutationHexagonBetween C.column C.turnRow C.oppositeTurnRow x y) :
    P ∈ G.commutationHexagons C x y ↔
      P.elim (fun Q => Q ∈ G.hexagons C x y) (fun Q => Q ∈ G.initialHexagons C x y) := by
  classical
  rcases P with P | P <;> simp [commutationHexagons]

/-- The counted commutation pentagons of either turn-side kind. -/
noncomputable def commutationPentagons (x y : GridState n) :
    Finset (GridCommutationPentagonBetween C.column C.turnRow x y) :=
  (G.pentagons C x y).disjSum (G.initialPentagons C x y)

/-- A commutation pentagon is counted exactly when the corresponding pentagon of its kind is
counted. -/
@[simp]
theorem mem_commutationPentagons {x y : GridState n}
    (P : GridCommutationPentagonBetween C.column C.turnRow x y) :
    P ∈ G.commutationPentagons C x y ↔
      P.elim (fun Q => Q ∈ G.pentagons C x y) (fun Q => Q ∈ G.initialPentagons C x y) := by
  classical
  rcases P with P | P <;> simp [commutationPentagons]

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

/-- The coefficient that counts commutation hexagons of either turn-side kind. -/
noncomputable def commutationHexagonCoefficient (x y : GridState n) :
    MvPolynomial (Fin n) R :=
  G.hexagonCoefficient R C x y + G.initialHexagonCoefficient R C x y

/-- The commutation hexagon coefficient is the sum of the two turn-side coefficients. -/
theorem commutationHexagonCoefficient_def (x y : GridState n) :
    G.commutationHexagonCoefficient C R x y =
      G.hexagonCoefficient R C x y + G.initialHexagonCoefficient R C x y := (rfl)

/-- The coefficient that counts commutation pentagons of either turn-side kind. -/
noncomputable def commutationPentagonCoefficient (x y : GridState n) :
    MvPolynomial (Fin n) R :=
  G.pentagonCoefficient R C x y + G.initialPentagonCoefficient R C x y

/-- The commutation pentagon coefficient is the sum of the two turn-side coefficients. -/
theorem commutationPentagonCoefficient_def (x y : GridState n) :
    G.commutationPentagonCoefficient C R x y =
      G.pentagonCoefficient R C x y + G.initialPentagonCoefficient R C x y := (rfl)

/-- The sum of the two kinds of hexagon coefficients is the sum of their combined weights. -/
theorem commutationHexagonCoefficient_eq_sum_weight (x y : GridState n) :
    G.commutationHexagonCoefficient C R x y =
      ∑ P ∈ G.commutationHexagons C x y, G.commutationHexagonWeight C R P := by
  rw [G.commutationHexagonCoefficient_def C R, G.hexagonCoefficient_def R C x y,
    G.initialHexagonCoefficient_def R C x y, commutationHexagons, Finset.sum_disjSum]
  simp only [commutationHexagonWeight_inl, commutationHexagonWeight_inr]

/-- The sum of the two kinds of pentagon coefficients is the sum of their combined weights. -/
theorem commutationPentagonCoefficient_eq_sum_weight (x y : GridState n) :
    G.commutationPentagonCoefficient C R x y =
      ∑ P ∈ G.commutationPentagons C x y, G.commutationPentagonWeight C R P := by
  rw [G.commutationPentagonCoefficient_def C R, G.pentagonCoefficient_def R C x y,
    G.initialPentagonCoefficient_def R C x y, commutationPentagons, Finset.sum_disjSum]
  simp only [commutationPentagonWeight_inl, commutationPentagonWeight_inr]

/-- The hexagon--rectangle matrix product is the sum of the weights of the counted composite
domains. -/
theorem sum_commutationHexagonCoefficient_mul_unblockedCoefficient (x z : GridState n) :
    ∑ y : GridState n,
        G.commutationHexagonCoefficient C R x y * G.unblockedCoefficient R y z =
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
        G.commutationHexagonCoefficient C R y z =
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
            (G.commutationPentagonCoefficient C R x y) *
          (G.swapColumns C.column b).commutationPentagonCoefficient C.reverse R y z =
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
  simp_rw [← G.commutationHexagonCoefficient_def C R,
    ← G.commutationPentagonCoefficient_def C R,
    ← (G.swapColumns C.column b).commutationPentagonCoefficient_def C.reverse R,
    Finset.sum_add_distrib,
    G.sum_commutationHexagonCoefficient_mul_unblockedCoefficient C R,
    G.sum_unblockedCoefficient_mul_commutationHexagonCoefficient C R,
    G.sum_rename_commutationPentagonCoefficient_mul_commutationPentagonCoefficient C R]

end GridDiagram

end TauCeti
