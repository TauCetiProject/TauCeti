/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Basic

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
between the two turn sides while avoiding four parallel decomposition structures. The three
structures here expose their intermediate state and constituent domains, have extensionality
lemmas, and their counted finite families have membership characterizations.

## Main results

* `TauCeti.GridDiagram.sum_commutationHexagonCoefficient_mul_unblockedCoefficient` and
  `TauCeti.GridDiagram.sum_unblockedCoefficient_mul_commutationHexagonCoefficient` rewrite the
  two rectangle--hexagon matrix products as composite-domain sums.
* `TauCeti.GridDiagram.sum_commutationPentagonCoefficient_mul_reverseCoefficient` rewrites the
  round-trip commutation coefficient as a sum over pairs of pentagons.
* `TauCeti.GridDiagram.unblockedDifferential_commutationHomotopy_add_eq_iff_decompositions`
  states the homotopy equation entirely in terms of the three finite domain families.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Section 5.1, and
Manolescu--Ozsváth--Szabó--Thurston, *On combinatorial link Floer homology*, Section 3.1
(arXiv:math/0610559).
-/

public section

namespace TauCeti

/-- A commutation hexagon is either a hexagon turning on its terminal side or one turning on its
initial side. -/
abbrev GridCommutationHexagonBetween {n : ℕ} (a s s' : Fin n) (x y : GridState n) :=
  GridHexagonBetween a s' s x y ⊕ GridInitialHexagonBetween a s s' x y

/-- A commutation pentagon is either a pentagon turning on its terminal side or one turning on its
initial side. -/
abbrev GridCommutationPentagonBetween {n : ℕ} (a s : Fin n) (x y : GridState n) :=
  GridPentagonBetween a s x y ⊕ GridInitialPentagonBetween a s x y

/-- A two-step domain consisting of a commutation hexagon followed by a rectangle. -/
structure GridHexagonRectangleDecomposition {n : ℕ} (a s s' : Fin n)
    (x z : GridState n) where
  /-- The grid state at which the hexagon and rectangle meet. -/
  middle : GridState n
  /-- The first domain, a hexagon of either kind. -/
  hexagon : GridCommutationHexagonBetween a s s' x middle
  /-- The second domain, an oriented rectangle. -/
  rectangle : GridRectangleBetween middle z

/-- A two-step domain consisting of a rectangle followed by a commutation hexagon. -/
structure GridRectangleHexagonDecomposition {n : ℕ} (a s s' : Fin n)
    (x z : GridState n) where
  /-- The grid state at which the rectangle and hexagon meet. -/
  middle : GridState n
  /-- The first domain, an oriented rectangle. -/
  rectangle : GridRectangleBetween x middle
  /-- The second domain, a hexagon of either kind. -/
  hexagon : GridCommutationHexagonBetween a s s' middle z

/-- A two-step domain consisting of a commutation pentagon followed by a pentagon for the reverse
commutation. -/
structure GridPentagonPairDecomposition {n : ℕ} (a s b t : Fin n)
    (x z : GridState n) where
  /-- The grid state at which the two pentagons meet. -/
  middle : GridState n
  /-- The pentagon for the forward commutation. -/
  first : GridCommutationPentagonBetween a s x middle
  /-- The pentagon for the reverse commutation. -/
  second : GridCommutationPentagonBetween b t middle z

namespace GridHexagonRectangleDecomposition

variable {n : ℕ} {a s s' : Fin n} {x z : GridState n}

/-- Two hexagon--rectangle decompositions are equal when their intermediate states and domains
agree. -/
@[ext]
theorem ext {D E : GridHexagonRectangleDecomposition a s s' x z}
    (hmiddle : D.middle = E.middle) (hhexagon : HEq D.hexagon E.hexagon)
    (hrectangle : HEq D.rectangle E.rectangle) : D = E := by
  cases D
  cases E
  simp_all

private def sigmaEquiv :
    GridHexagonRectangleDecomposition a s s' x z ≃
      Σ y : GridState n,
        Σ _hexagon : GridCommutationHexagonBetween a s s' x y, GridRectangleBetween y z where
  toFun D := ⟨D.middle, D.hexagon, D.rectangle⟩
  invFun D := ⟨D.1, D.2.1, D.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The finite family of hexagon--rectangle decompositions selected by prescribed families of
hexagons and rectangles. -/
noncomputable def decompositionsOf
    (hexagons : ∀ u v : GridState n,
      Finset (GridCommutationHexagonBetween a s s' u v))
    (rectangles : ∀ u v : GridState n, Finset (GridRectangleBetween u v))
    (x z : GridState n) : Finset (GridHexagonRectangleDecomposition a s s' x z) := by
  classical
  exact ((Finset.univ.sigma fun y => (hexagons x y).sigma fun _ => rectangles y z).map
    (sigmaEquiv (a := a) (s := s) (s' := s') (x := x) (z := z)).symm.toEmbedding)

/-- Membership in `decompositionsOf` is membership of both constituent domains. -/
@[simp]
theorem mem_decompositionsOf
    (hexagons : ∀ u v : GridState n,
      Finset (GridCommutationHexagonBetween a s s' u v))
    (rectangles : ∀ u v : GridState n, Finset (GridRectangleBetween u v))
    (D : GridHexagonRectangleDecomposition a s s' x z) :
    D ∈ decompositionsOf hexagons rectangles x z ↔
      D.hexagon ∈ hexagons x D.middle ∧ D.rectangle ∈ rectangles D.middle z := by
  classical
  simp [decompositionsOf, sigmaEquiv]

/-- A sum over selected hexagon--rectangle decompositions is the corresponding iterated sum. -/
theorem sum_decompositionsOf {M : Type*} [AddCommMonoid M]
    (hexagons : ∀ u v : GridState n,
      Finset (GridCommutationHexagonBetween a s s' u v))
    (rectangles : ∀ u v : GridState n, Finset (GridRectangleBetween u v))
    (w : ∀ y, GridCommutationHexagonBetween a s s' x y → GridRectangleBetween y z → M) :
    ∑ D ∈ decompositionsOf hexagons rectangles x z, w D.middle D.hexagon D.rectangle =
      ∑ y, ∑ P ∈ hexagons x y, ∑ r ∈ rectangles y z, w y P r := by
  classical
  simp [decompositionsOf, sigmaEquiv, Finset.sum_sigma']

end GridHexagonRectangleDecomposition

namespace GridRectangleHexagonDecomposition

variable {n : ℕ} {a s s' : Fin n} {x z : GridState n}

/-- Two rectangle--hexagon decompositions are equal when their intermediate states and domains
agree. -/
@[ext]
theorem ext {D E : GridRectangleHexagonDecomposition a s s' x z}
    (hmiddle : D.middle = E.middle) (hrectangle : HEq D.rectangle E.rectangle)
    (hhexagon : HEq D.hexagon E.hexagon) : D = E := by
  cases D
  cases E
  simp_all

private def sigmaEquiv :
    GridRectangleHexagonDecomposition a s s' x z ≃
      Σ y : GridState n,
        Σ _rectangle : GridRectangleBetween x y, GridCommutationHexagonBetween a s s' y z where
  toFun D := ⟨D.middle, D.rectangle, D.hexagon⟩
  invFun D := ⟨D.1, D.2.1, D.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The finite family of rectangle--hexagon decompositions selected by prescribed families of
rectangles and hexagons. -/
noncomputable def decompositionsOf
    (rectangles : ∀ u v : GridState n, Finset (GridRectangleBetween u v))
    (hexagons : ∀ u v : GridState n,
      Finset (GridCommutationHexagonBetween a s s' u v))
    (x z : GridState n) : Finset (GridRectangleHexagonDecomposition a s s' x z) := by
  classical
  exact ((Finset.univ.sigma fun y => (rectangles x y).sigma fun _ => hexagons y z).map
    (sigmaEquiv (a := a) (s := s) (s' := s') (x := x) (z := z)).symm.toEmbedding)

/-- Membership in `decompositionsOf` is membership of both constituent domains. -/
@[simp]
theorem mem_decompositionsOf
    (rectangles : ∀ u v : GridState n, Finset (GridRectangleBetween u v))
    (hexagons : ∀ u v : GridState n,
      Finset (GridCommutationHexagonBetween a s s' u v))
    (D : GridRectangleHexagonDecomposition a s s' x z) :
    D ∈ decompositionsOf rectangles hexagons x z ↔
      D.rectangle ∈ rectangles x D.middle ∧ D.hexagon ∈ hexagons D.middle z := by
  classical
  simp [decompositionsOf, sigmaEquiv]

/-- A sum over selected rectangle--hexagon decompositions is the corresponding iterated sum. -/
theorem sum_decompositionsOf {M : Type*} [AddCommMonoid M]
    (rectangles : ∀ u v : GridState n, Finset (GridRectangleBetween u v))
    (hexagons : ∀ u v : GridState n,
      Finset (GridCommutationHexagonBetween a s s' u v))
    (w : ∀ y, GridRectangleBetween x y → GridCommutationHexagonBetween a s s' y z → M) :
    ∑ D ∈ decompositionsOf rectangles hexagons x z, w D.middle D.rectangle D.hexagon =
      ∑ y, ∑ r ∈ rectangles x y, ∑ P ∈ hexagons y z, w y r P := by
  classical
  simp [decompositionsOf, sigmaEquiv, Finset.sum_sigma']

end GridRectangleHexagonDecomposition

namespace GridPentagonPairDecomposition

variable {n : ℕ} {a s b t : Fin n} {x z : GridState n}

/-- Two pentagon-pair decompositions are equal when their intermediate states and both pentagons
agree. -/
@[ext]
theorem ext {D E : GridPentagonPairDecomposition a s b t x z}
    (hmiddle : D.middle = E.middle) (hfirst : HEq D.first E.first)
    (hsecond : HEq D.second E.second) : D = E := by
  cases D
  cases E
  simp_all

private def sigmaEquiv :
    GridPentagonPairDecomposition a s b t x z ≃
      Σ y : GridState n,
        Σ _first : GridCommutationPentagonBetween a s x y,
          GridCommutationPentagonBetween b t y z where
  toFun D := ⟨D.middle, D.first, D.second⟩
  invFun D := ⟨D.1, D.2.1, D.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The finite family of pentagon-pair decompositions selected by prescribed forward and reverse
pentagon families. -/
noncomputable def decompositionsOf
    (first : ∀ u v : GridState n, Finset (GridCommutationPentagonBetween a s u v))
    (second : ∀ u v : GridState n, Finset (GridCommutationPentagonBetween b t u v))
    (x z : GridState n) : Finset (GridPentagonPairDecomposition a s b t x z) := by
  classical
  exact ((Finset.univ.sigma fun y => (first x y).sigma fun _ => second y z).map
    (sigmaEquiv (a := a) (s := s) (b := b) (t := t) (x := x) (z := z)).symm.toEmbedding)

/-- Membership in `decompositionsOf` is membership of both pentagons. -/
@[simp]
theorem mem_decompositionsOf
    (first : ∀ u v : GridState n, Finset (GridCommutationPentagonBetween a s u v))
    (second : ∀ u v : GridState n, Finset (GridCommutationPentagonBetween b t u v))
    (D : GridPentagonPairDecomposition a s b t x z) :
    D ∈ decompositionsOf first second x z ↔
      D.first ∈ first x D.middle ∧ D.second ∈ second D.middle z := by
  classical
  simp [decompositionsOf, sigmaEquiv]

/-- A sum over selected pentagon-pair decompositions is the corresponding iterated sum. -/
theorem sum_decompositionsOf {M : Type*} [AddCommMonoid M]
    (first : ∀ u v : GridState n, Finset (GridCommutationPentagonBetween a s u v))
    (second : ∀ u v : GridState n, Finset (GridCommutationPentagonBetween b t u v))
    (w : ∀ y, GridCommutationPentagonBetween a s x y →
      GridCommutationPentagonBetween b t y z → M) :
    ∑ D ∈ decompositionsOf first second x z, w D.middle D.first D.second =
      ∑ y, ∑ P ∈ first x y, ∑ Q ∈ second y z, w y P Q := by
  classical
  simp [decompositionsOf, sigmaEquiv, Finset.sum_sigma']

end GridPentagonPairDecomposition

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
  GridHexagonRectangleDecomposition.decompositionsOf (G.commutationHexagons C)
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
  GridRectangleHexagonDecomposition.decompositionsOf G.unblockedRectangles
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
  GridPentagonPairDecomposition.decompositionsOf (G.commutationPentagons C)
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

/-- The weight of a counted rectangle followed by a hexagon. -/
noncomputable def rectangleHexagonWeight {x z : GridState n}
    (D : GridRectangleHexagonDecomposition C.column C.turnRow C.oppositeTurnRow x z) :
    MvPolynomial (Fin n) R :=
  G.OMonomial R D.rectangle.toGridRectangle * G.commutationHexagonWeight C R D.hexagon

/-- The weight of a forward pentagon followed by a reverse pentagon. The first factor is renamed
because the forward commutation map is semilinear. -/
noncomputable def pentagonPairWeight {x z : GridState n}
    (D : GridPentagonPairDecomposition C.column C.turnRow C.reverse.column
      C.reverse.turnRow x z) :
    MvPolynomial (Fin n) R :=
  MvPolynomial.rename (Equiv.swap C.column b) (G.commutationPentagonWeight C R D.first) *
    (G.swapColumns C.column b).commutationPentagonWeight C.reverse R D.second

/-- The sum of the two kinds of hexagon coefficients is the sum of their combined weights. -/
theorem commutationHexagonCoefficient_eq_sum_weight (x y : GridState n) :
    G.hexagonCoefficient R C x y + G.initialHexagonCoefficient R C x y =
      ∑ P ∈ G.commutationHexagons C x y, G.commutationHexagonWeight C R P := by
  rw [G.hexagonCoefficient_def R C x y, G.initialHexagonCoefficient_def R C x y,
    commutationHexagons, Finset.sum_disjSum]
  rfl

/-- The sum of the two kinds of pentagon coefficients is the sum of their combined weights. -/
theorem commutationPentagonCoefficient_eq_sum_weight (x y : GridState n) :
    G.pentagonCoefficient R C x y + G.initialPentagonCoefficient R C x y =
      ∑ P ∈ G.commutationPentagons C x y, G.commutationPentagonWeight C R P := by
  rw [G.pentagonCoefficient_def R C x y, G.initialPentagonCoefficient_def R C x y,
    commutationPentagons, Finset.sum_disjSum]
  rfl

/-- The hexagon--rectangle matrix product is the sum of the weights of the counted composite
domains. -/
theorem sum_commutationHexagonCoefficient_mul_unblockedCoefficient (x z : GridState n) :
    ∑ y : GridState n,
        (G.hexagonCoefficient R C x y + G.initialHexagonCoefficient R C x y) *
          G.unblockedCoefficient R y z =
      ∑ D ∈ G.hexagonRectangleDecompositions C x z, G.hexagonRectangleWeight C R D := by
  simp_rw [G.commutationHexagonCoefficient_eq_sum_weight C R,
    G.unblockedCoefficient_def R, Finset.sum_mul_sum]
  exact (GridHexagonRectangleDecomposition.sum_decompositionsOf
    (G.commutationHexagons C) G.unblockedRectangles
    (fun _ P r => G.commutationHexagonWeight C R P * G.OMonomial R r.toGridRectangle)).symm

/-- The rectangle--hexagon matrix product is the sum of the weights of the counted composite
domains. -/
theorem sum_unblockedCoefficient_mul_commutationHexagonCoefficient (x z : GridState n) :
    ∑ y : GridState n, G.unblockedCoefficient R x y *
        (G.hexagonCoefficient R C y z + G.initialHexagonCoefficient R C y z) =
      ∑ D ∈ G.rectangleHexagonDecompositions C x z, G.rectangleHexagonWeight C R D := by
  simp_rw [G.unblockedCoefficient_def R, G.commutationHexagonCoefficient_eq_sum_weight C R,
    Finset.sum_mul_sum]
  exact (GridRectangleHexagonDecomposition.sum_decompositionsOf G.unblockedRectangles
    (G.commutationHexagons C)
    (fun _ r P => G.OMonomial R r.toGridRectangle * G.commutationHexagonWeight C R P)).symm

/-- The forward--reverse pentagon matrix product is the sum of the weights of the counted
pentagon pairs. -/
theorem sum_commutationPentagonCoefficient_mul_reverseCoefficient (x z : GridState n) :
    ∑ y : GridState n,
        MvPolynomial.rename (Equiv.swap C.column b)
            (G.pentagonCoefficient R C x y + G.initialPentagonCoefficient R C x y) *
          ((G.swapColumns C.column b).pentagonCoefficient R C.reverse y z +
            (G.swapColumns C.column b).initialPentagonCoefficient R C.reverse y z) =
      ∑ D ∈ G.pentagonPairDecompositions C x z, G.pentagonPairWeight C R D := by
  simp_rw [G.commutationPentagonCoefficient_eq_sum_weight C R,
    (G.swapColumns C.column b).commutationPentagonCoefficient_eq_sum_weight C.reverse R,
    map_sum, Finset.sum_mul_sum]
  exact (GridPentagonPairDecomposition.sum_decompositionsOf (G.commutationPentagons C)
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
    G.sum_commutationPentagonCoefficient_mul_reverseCoefficient C R]

end GridDiagram

end TauCeti
