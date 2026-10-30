/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Diagonal
public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Disjoint
import Mathlib.Algebra.CharP.Two

/-!
# Composite domains of the crossing change homotopy equation

Let `C` be a column turn at the columns `a` and `b = finRotate n a` of a grid diagram `G`, turning
in row `s`, and let `t` be a second row. Write `G' = G.swapColumns a b`, `∂` for the unblocked
differential of `G`, `Φ : GC⁻(G) → GC⁻(G')` for the commutation map of `C`,
`Ψ : GC⁻(G') → GC⁻(G)` for the commutation map of `G'` at `C.withTurnRow t`, and
`H : GC⁻(G) → GC⁻(G)` for the crossing change homotopy `GridDiagram.crossingChangeHomotopy`. For
interleaving columns, with `s` and `t` the rows of the turn points of the crossing change maps,
Ozsváth--Stipsicz--Szabó's homotopy equation reads `∂H + H∂ = V + ΨΦ` over `𝔽₂`, for the variable
`V` of one of the two columns; in general the multiplier is the annulus weight
`GridDiagram.crossingChangeAnnulusWeight`, whose diagonal coefficients are already known
(`GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_single_apply_self`).

This file rewrites the off-diagonal coefficients of `∂H + H∂` as sums over composite domains, a
counted hexagon of either shape followed by an empty rectangle avoiding the `X`-markings or
preceded by one, and cancels those whose two rectangles have disjoint pairs of vertical sides.
The hexagons have the shapes of the commutation homotopy,
`TauCeti.GridCommutationHexagonBetween a s t`, so the composite domain types and the reordering
of disjoint composites (`TauCeti.GridHexagonRectangleDecomposition.commute`) are those of the
commutation homotopy equation. Only the markings a hexagon carries differ: they are those of its
`crossingCoveredSquares`. Reordering a disjoint composite does not change the toroidal rectangles,
hence neither the markings each piece carries, so it is a weight-preserving bijection between the
two orders of composition, and the two disjoint sums cancel in characteristic two.

What remains of the homotopy equation is the off-diagonal identity between the composites whose
rectangles share a vertical side and the pairs of pentagons counted by `ΨΦ`
(`GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_iff_overlap`). That identity is
not proved here.

## Main definitions

* `TauCeti.GridCommutationHexagonBetween.crossingCoveredSquares`: the squares whose markings lie
  inside a crossing-change hexagon of either shape.
* `TauCeti.GridDiagram.crossingChangeCommutationHexagons` and
  `TauCeti.GridDiagram.crossingChangeCommutationHexagonWeight`: the counted crossing-change
  hexagons of either shape and their weights.
* `TauCeti.GridDiagram.crossingChangeHexagonRectangleDecompositions` and
  `TauCeti.GridDiagram.crossingChangeRectangleHexagonDecompositions`, with weights
  `TauCeti.GridDiagram.crossingChangeHexagonRectangleWeight` and
  `TauCeti.GridDiagram.crossingChangeRectangleHexagonWeight`: the composite domains counted by
  `∂H` and `H∂`.

## Main results

* `TauCeti.GridDiagram.sum_crossingChangeHexagonCoefficient_mul_unblockedCoefficient` and
  `TauCeti.GridDiagram.sum_unblockedCoefficient_mul_crossingChangeHexagonCoefficient`: the matrix
  coefficients of `∂H` and `H∂` as sums over composite domains.
* `TauCeti.GridDiagram.sum_disjoint_crossingChangeRectangleHexagonWeight_eq`: the composites with
  disjoint vertical sides have the same total weight in both orders.
* `TauCeti.GridDiagram.sum_crossingChangeHexagonRectangleWeight_add_sum_eq_overlap`: in
  characteristic two, only the composites sharing a vertical side contribute.
* `TauCeti.GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_iff_overlap`: when
  `s ≠ t` and the annulus squares carry no `X`-marking, the homotopy equation
  `∂H + H∂ = w + ΨΦ`, with `w` the annulus weight, holds on every chain over a commutative
  semiring of characteristic two exactly when, off the diagonal, the composites sharing a vertical
  side have the total weight of the pentagon pairs.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Sections 5.1 and 6.1: the juxtaposition argument for the hexagon
  homotopies of commutation and of a crossing change.
* M. Kendall, *Crossing change maps in filtered grid homology*, arXiv:2303.04227, Section 3: the
  homotopy equations for the hexagons with corners at the two turn points.
-/

public section

namespace TauCeti

namespace GridCommutationHexagonBetween

variable {n : ℕ} {a s s' : Fin n} {x y : GridState n}

/-- The squares whose markings lie inside a crossing-change hexagon of either shape: the
`crossingCoveredSquares` of the terminal-side or of the initial-side hexagon. -/
noncomputable def crossingCoveredSquares (P : GridCommutationHexagonBetween a s s' x y) :
    Finset (Fin n × Fin n) :=
  P.elim GridHexagonBetween.crossingCoveredSquares GridInitialHexagonBetween.crossingCoveredSquares

/-- The squares carrying the markings of a terminal-side crossing-change hexagon. -/
@[simp]
theorem crossingCoveredSquares_inl (P : GridHexagonBetween a s' s x y) :
    crossingCoveredSquares (Sum.inl P : GridCommutationHexagonBetween a s s' x y) =
      P.crossingCoveredSquares := (rfl)

/-- The squares carrying the markings of an initial-side crossing-change hexagon. -/
@[simp]
theorem crossingCoveredSquares_inr (P : GridInitialHexagonBetween a s s' x y) :
    crossingCoveredSquares (Sum.inr P : GridCommutationHexagonBetween a s s' x y) =
      P.crossingCoveredSquares := (rfl)

/-- The squares carrying the markings of a crossing-change hexagon of either shape depend only on
its underlying toroidal rectangle, which also determines its shape. -/
theorem crossingCoveredSquares_eq_of_toGridRectangle_eq {u v : GridState n}
    {P : GridCommutationHexagonBetween a s s' x y} {Q : GridCommutationHexagonBetween a s s' u v}
    (h : P.toGridRectangleBetween.toGridRectangle = Q.toGridRectangleBetween.toGridRectangle) :
    P.crossingCoveredSquares = Q.crossingCoveredSquares := by
  -- A terminal-side and an initial-side hexagon cannot share a rectangle: only the latter has
  -- the replaced grid line as its initial side.
  have hl := congrArg GridRectangle.left h
  simp only [GridRectangleBetween.toGridRectangle_left] at hl
  cases P <;> cases Q <;>
    simp only [toGridRectangleBetween_inl, toGridRectangleBetween_inr, crossingCoveredSquares_inl,
      crossingCoveredSquares_inr] at h hl ⊢
  · exact GridHexagonBetween.crossingCoveredSquares_eq_of_toGridRectangle_eq _ _ h
  · exact (GridHexagonBetween.left_ne _ (hl.trans (GridInitialHexagonBetween.left_eq _))).elim
  · exact (GridHexagonBetween.left_ne _ (hl.symm.trans (GridInitialHexagonBetween.left_eq _))).elim
  · exact GridInitialHexagonBetween.crossingCoveredSquares_eq_of_toGridRectangle_eq _ _ h

end GridCommutationHexagonBetween

namespace GridRectangleHexagonDecomposition

variable {n : ℕ} {a s s' : Fin n} {x z : GridState n}

/-- Reordering a disjoint rectangle--hexagon domain preserves the squares carrying the markings of
the hexagon in a crossing change. -/
@[simp]
theorem commute_hexagon_crossingCoveredSquares (D : GridRectangleHexagonDecomposition a s s' x z)
    (h : D.toRectangleDecomposition.HasDisjointSides) :
    (D.commute h).first.crossingCoveredSquares = D.second.crossingCoveredSquares :=
  GridCommutationHexagonBetween.crossingCoveredSquares_eq_of_toGridRectangle_eq <|
    (congrArg (fun E => E.first.toGridRectangle) (D.commute_toRectangleDecomposition h)).trans
      (D.toRectangleDecomposition.commute_first_toGridRectangle h)

end GridRectangleHexagonDecomposition

namespace GridHexagonRectangleDecomposition

variable {n : ℕ} {a s s' : Fin n} {x z : GridState n}

/-- Reordering a disjoint hexagon--rectangle domain preserves the squares carrying the markings of
the hexagon in a crossing change. -/
@[simp]
theorem commute_hexagon_crossingCoveredSquares (D : GridHexagonRectangleDecomposition a s s' x z)
    (h : D.toRectangleDecomposition.HasDisjointSides) :
    (D.commute h).second.crossingCoveredSquares = D.first.crossingCoveredSquares :=
  GridCommutationHexagonBetween.crossingCoveredSquares_eq_of_toGridRectangle_eq <|
    (congrArg (fun E => E.second.toGridRectangle) (D.commute_toRectangleDecomposition h)).trans
      (D.toRectangleDecomposition.commute_second_toGridRectangle h)

end GridHexagonRectangleDecomposition

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-! ### Counted hexagons of either shape -/

section Hexagons

variable (C : ColumnTurn n) (t : Fin n)

/-- The counted hexagons of a crossing change, of either shape: those of
`GridDiagram.crossingChangeHexagons` and of `GridDiagram.crossingChangeInitialHexagons`. -/
noncomputable def crossingChangeCommutationHexagons (x y : GridState n) :
    Finset (GridCommutationHexagonBetween C.column C.turnRow t x y) :=
  (G.crossingChangeHexagons C t x y).disjSum (G.crossingChangeInitialHexagons C t x y)

/-- A crossing-change hexagon of either shape is counted exactly when its underlying rectangle is
empty and the squares carrying its markings avoid every `X`-marking. -/
@[simp]
theorem mem_crossingChangeCommutationHexagons {x y : GridState n}
    (P : GridCommutationHexagonBetween C.column C.turnRow t x y) :
    P ∈ G.crossingChangeCommutationHexagons C t x y ↔
      P.toGridRectangleBetween.IsEmpty ∧ Disjoint P.crossingCoveredSquares G.XSet := by
  cases P <;> simp [crossingChangeCommutationHexagons]

variable (R : Type*) [CommSemiring R]

/-- The weight of a crossing-change hexagon of either shape: the product of the variables of the
`O`-markings it carries. -/
noncomputable def crossingChangeCommutationHexagonWeight {a s s' : Fin n} {x y : GridState n}
    (P : GridCommutationHexagonBetween a s s' x y) : MvPolynomial (Fin n) R :=
  P.elim (G.crossingChangeHexagonWeight R) (G.crossingChangeInitialHexagonWeight R)

/-- The weight of a terminal-side crossing-change hexagon. -/
@[simp]
theorem crossingChangeCommutationHexagonWeight_inl {a s s' : Fin n} {x y : GridState n}
    (P : GridHexagonBetween a s' s x y) :
    G.crossingChangeCommutationHexagonWeight R
        (Sum.inl P : GridCommutationHexagonBetween a s s' x y) =
      G.crossingChangeHexagonWeight R P := (rfl)

/-- The weight of an initial-side crossing-change hexagon. -/
@[simp]
theorem crossingChangeCommutationHexagonWeight_inr {a s s' : Fin n} {x y : GridState n}
    (P : GridInitialHexagonBetween a s s' x y) :
    G.crossingChangeCommutationHexagonWeight R
        (Sum.inr P : GridCommutationHexagonBetween a s s' x y) =
      G.crossingChangeInitialHexagonWeight R P := (rfl)

/-- The weight of a crossing-change hexagon of either shape is the squarefree monomial of the
`O`-markings it carries. -/
theorem crossingChangeCommutationHexagonWeight_eq_monomial {a s s' : Fin n} {x y : GridState n}
    (P : GridCommutationHexagonBetween a s s' x y) :
    G.crossingChangeCommutationHexagonWeight R P =
      MvPolynomial.monomial
        (∑ c ∈ G.OColumnsOfSquares P.crossingCoveredSquares, Finsupp.single c 1) 1 := by
  cases P with
  | inl P => exact G.crossingChangeHexagonWeight_eq_monomial R P
  | inr P => exact G.crossingChangeInitialHexagonWeight_eq_monomial R P

/-- The weight of a crossing-change hexagon is determined by the squares carrying its markings. -/
theorem crossingChangeCommutationHexagonWeight_eq_of_crossingCoveredSquares_eq {a s s' : Fin n}
    {x y u v : GridState n} {P : GridCommutationHexagonBetween a s s' x y}
    {Q : GridCommutationHexagonBetween a s s' u v}
    (h : P.crossingCoveredSquares = Q.crossingCoveredSquares) :
    G.crossingChangeCommutationHexagonWeight R P =
      G.crossingChangeCommutationHexagonWeight R Q := by
  rw [crossingChangeCommutationHexagonWeight_eq_monomial,
    crossingChangeCommutationHexagonWeight_eq_monomial, h]

/-- The matrix coefficient of the crossing change homotopy is the sum of the weights of the
counted hexagons of either shape. -/
theorem crossingChangeHexagonCoefficient_eq_sum_weight (x y : GridState n) :
    G.crossingChangeHexagonCoefficient R C t x y =
      ∑ P ∈ G.crossingChangeCommutationHexagons C t x y,
        G.crossingChangeCommutationHexagonWeight R P := by
  rw [crossingChangeHexagonCoefficient_def, crossingChangeCommutationHexagons,
    Finset.sum_disjSum]
  simp only [crossingChangeCommutationHexagonWeight_inl, crossingChangeCommutationHexagonWeight_inr]

end Hexagons

/-! ### Composite domains -/

section Composites

variable (C : ColumnTurn n) (t : Fin n)

/-- The hexagon--rectangle decompositions counted in the coefficients of the differential after the
crossing change homotopy: a counted crossing-change hexagon of either shape followed by an empty
rectangle avoiding the `X`-markings. -/
noncomputable def crossingChangeHexagonRectangleDecompositions (x z : GridState n) :
    Finset (GridHexagonRectangleDecomposition C.column C.turnRow t x z) :=
  GridTwoStepDecomposition.decompositionsOf (G.crossingChangeCommutationHexagons C t)
    G.unblockedRectangles x z

/-- Membership in the counted hexagon--rectangle family is countedness of both domains. -/
@[simp]
theorem mem_crossingChangeHexagonRectangleDecompositions {x z : GridState n}
    (D : GridHexagonRectangleDecomposition C.column C.turnRow t x z) :
    D ∈ G.crossingChangeHexagonRectangleDecompositions C t x z ↔
      D.hexagon ∈ G.crossingChangeCommutationHexagons C t x D.middle ∧
        D.rectangle ∈ G.unblockedRectangles D.middle z := by
  classical
  simp only [crossingChangeHexagonRectangleDecompositions,
    GridTwoStepDecomposition.mem_decompositionsOf]

/-- The rectangle--hexagon decompositions counted in the coefficients of the crossing change
homotopy after the differential: an empty rectangle avoiding the `X`-markings followed by a counted
crossing-change hexagon of either shape. -/
noncomputable def crossingChangeRectangleHexagonDecompositions (x z : GridState n) :
    Finset (GridRectangleHexagonDecomposition C.column C.turnRow t x z) :=
  GridTwoStepDecomposition.decompositionsOf G.unblockedRectangles
    (G.crossingChangeCommutationHexagons C t) x z

/-- Membership in the counted rectangle--hexagon family is countedness of both domains. -/
@[simp]
theorem mem_crossingChangeRectangleHexagonDecompositions {x z : GridState n}
    (D : GridRectangleHexagonDecomposition C.column C.turnRow t x z) :
    D ∈ G.crossingChangeRectangleHexagonDecompositions C t x z ↔
      D.rectangle ∈ G.unblockedRectangles x D.middle ∧
        D.hexagon ∈ G.crossingChangeCommutationHexagons C t D.middle z := by
  classical
  simp only [crossingChangeRectangleHexagonDecompositions,
    GridTwoStepDecomposition.mem_decompositionsOf]

variable (R : Type*) [CommSemiring R]

/-- The weight of a crossing-change hexagon followed by a rectangle: the product of their
weights. -/
noncomputable def crossingChangeHexagonRectangleWeight {x z : GridState n}
    (D : GridHexagonRectangleDecomposition C.column C.turnRow t x z) : MvPolynomial (Fin n) R :=
  G.crossingChangeCommutationHexagonWeight R D.hexagon * G.OMonomial R D.rectangle.toGridRectangle

/-- The weight of a hexagon--rectangle decomposition is the product of the two domain weights. -/
theorem crossingChangeHexagonRectangleWeight_def {x z : GridState n}
    (D : GridHexagonRectangleDecomposition C.column C.turnRow t x z) :
    G.crossingChangeHexagonRectangleWeight C t R D =
      G.crossingChangeCommutationHexagonWeight R D.hexagon *
        G.OMonomial R D.rectangle.toGridRectangle := (rfl)

/-- The weight of a rectangle followed by a crossing-change hexagon: the product of their
weights. -/
noncomputable def crossingChangeRectangleHexagonWeight {x z : GridState n}
    (D : GridRectangleHexagonDecomposition C.column C.turnRow t x z) : MvPolynomial (Fin n) R :=
  G.OMonomial R D.rectangle.toGridRectangle * G.crossingChangeCommutationHexagonWeight R D.hexagon

/-- The weight of a rectangle--hexagon decomposition is the product of the two domain weights. -/
theorem crossingChangeRectangleHexagonWeight_def {x z : GridState n}
    (D : GridRectangleHexagonDecomposition C.column C.turnRow t x z) :
    G.crossingChangeRectangleHexagonWeight C t R D =
      G.OMonomial R D.rectangle.toGridRectangle *
        G.crossingChangeCommutationHexagonWeight R D.hexagon := (rfl)

/-- The coefficient of `∂ ∘ H` from `x` to `z`, as a matrix product, is the sum of the weights of
the counted hexagon--rectangle decompositions. -/
theorem sum_crossingChangeHexagonCoefficient_mul_unblockedCoefficient (x z : GridState n) :
    ∑ y : GridState n,
        G.crossingChangeHexagonCoefficient R C t x y * G.unblockedCoefficient R y z =
      ∑ D ∈ G.crossingChangeHexagonRectangleDecompositions C t x z,
        G.crossingChangeHexagonRectangleWeight C t R D := by
  simp_rw [G.crossingChangeHexagonCoefficient_eq_sum_weight C t R, G.unblockedCoefficient_def R,
    Finset.sum_mul_sum]
  exact (GridTwoStepDecomposition.sum_decompositionsOf (G.crossingChangeCommutationHexagons C t)
    G.unblockedRectangles fun _ P r =>
      G.crossingChangeCommutationHexagonWeight R P * G.OMonomial R r.toGridRectangle).symm

/-- The coefficient of `H ∘ ∂` from `x` to `z`, as a matrix product, is the sum of the weights of
the counted rectangle--hexagon decompositions. -/
theorem sum_unblockedCoefficient_mul_crossingChangeHexagonCoefficient (x z : GridState n) :
    ∑ y : GridState n,
        G.unblockedCoefficient R x y * G.crossingChangeHexagonCoefficient R C t y z =
      ∑ D ∈ G.crossingChangeRectangleHexagonDecompositions C t x z,
        G.crossingChangeRectangleHexagonWeight C t R D := by
  simp_rw [G.unblockedCoefficient_def R, G.crossingChangeHexagonCoefficient_eq_sum_weight C t R,
    Finset.sum_mul_sum]
  exact (GridTwoStepDecomposition.sum_decompositionsOf G.unblockedRectangles
    (G.crossingChangeCommutationHexagons C t) fun _ r P =>
      G.OMonomial R r.toGridRectangle * G.crossingChangeCommutationHexagonWeight R P).symm

end Composites

/-! ### Cancelling composites with disjoint vertical sides -/

section Disjoint

variable (C : ColumnTurn n) (t : Fin n)

/-- Reordering a counted rectangle--hexagon domain with disjoint vertical sides gives a counted
hexagon--rectangle domain. -/
theorem commute_mem_crossingChangeHexagonRectangleDecompositions {x z : GridState n}
    (D : GridRectangleHexagonDecomposition C.column C.turnRow t x z)
    (h : D.toRectangleDecomposition.HasDisjointSides)
    (hD : D ∈ G.crossingChangeRectangleHexagonDecompositions C t x z) :
    D.commute h ∈ G.crossingChangeHexagonRectangleDecompositions C t x z := by
  obtain ⟨hr, hP⟩ := (G.mem_crossingChangeRectangleHexagonDecompositions C t D).mp hD
  obtain ⟨hrEmpty, hrX⟩ := (G.mem_unblockedRectangles _).mp hr
  obtain ⟨hPEmpty, hPX⟩ := (G.mem_crossingChangeCommutationHexagons C t _).mp hP
  have he₁ := D.toRectangleDecomposition.isEmpty_commute_first h hrEmpty hPEmpty
  have he₂ := D.toRectangleDecomposition.isEmpty_commute_second h hrEmpty hPEmpty
  rw [← D.commute_toRectangleDecomposition h] at he₁ he₂
  refine (G.mem_crossingChangeHexagonRectangleDecompositions C t _).mpr
    ⟨(G.mem_crossingChangeCommutationHexagons C t _).mpr ⟨he₁, ?_⟩,
      (G.mem_unblockedRectangles _).mpr ⟨he₂, ?_⟩⟩
  · rwa [D.commute_hexagon_crossingCoveredSquares h]
  · rwa [D.commute_rectangle_toGridRectangle h]

/-- Reordering a counted hexagon--rectangle domain with disjoint vertical sides gives a counted
rectangle--hexagon domain. -/
theorem commute_mem_crossingChangeRectangleHexagonDecompositions {x z : GridState n}
    (D : GridHexagonRectangleDecomposition C.column C.turnRow t x z)
    (h : D.toRectangleDecomposition.HasDisjointSides)
    (hD : D ∈ G.crossingChangeHexagonRectangleDecompositions C t x z) :
    D.commute h ∈ G.crossingChangeRectangleHexagonDecompositions C t x z := by
  obtain ⟨hP, hr⟩ := (G.mem_crossingChangeHexagonRectangleDecompositions C t D).mp hD
  obtain ⟨hPEmpty, hPX⟩ := (G.mem_crossingChangeCommutationHexagons C t _).mp hP
  obtain ⟨hrEmpty, hrX⟩ := (G.mem_unblockedRectangles _).mp hr
  have he₁ := D.toRectangleDecomposition.isEmpty_commute_first h hPEmpty hrEmpty
  have he₂ := D.toRectangleDecomposition.isEmpty_commute_second h hPEmpty hrEmpty
  rw [← D.commute_toRectangleDecomposition h] at he₁ he₂
  refine (G.mem_crossingChangeRectangleHexagonDecompositions C t _).mpr
    ⟨(G.mem_unblockedRectangles _).mpr ⟨he₁, ?_⟩,
      (G.mem_crossingChangeCommutationHexagons C t _).mpr ⟨he₂, ?_⟩⟩
  · rwa [D.commute_rectangle_toGridRectangle h]
  · rwa [D.commute_hexagon_crossingCoveredSquares h]

variable (R : Type*) [CommSemiring R]

/-- Reordering a rectangle--hexagon domain with disjoint vertical sides preserves its weight. -/
theorem crossingChangeHexagonRectangleWeight_commute {x z : GridState n}
    (D : GridRectangleHexagonDecomposition C.column C.turnRow t x z)
    (h : D.toRectangleDecomposition.HasDisjointSides) :
    G.crossingChangeHexagonRectangleWeight C t R (D.commute h) =
      G.crossingChangeRectangleHexagonWeight C t R D := by
  rw [crossingChangeHexagonRectangleWeight_def, crossingChangeRectangleHexagonWeight_def,
    G.crossingChangeCommutationHexagonWeight_eq_of_crossingCoveredSquares_eq R
      (D.commute_hexagon_crossingCoveredSquares h),
    D.commute_rectangle_toGridRectangle h, mul_comm]

/-- Reordering a hexagon--rectangle domain with disjoint vertical sides preserves its weight. -/
theorem crossingChangeRectangleHexagonWeight_commute {x z : GridState n}
    (D : GridHexagonRectangleDecomposition C.column C.turnRow t x z)
    (h : D.toRectangleDecomposition.HasDisjointSides) :
    G.crossingChangeRectangleHexagonWeight C t R (D.commute h) =
      G.crossingChangeHexagonRectangleWeight C t R D := by
  rw [crossingChangeHexagonRectangleWeight_def, crossingChangeRectangleHexagonWeight_def,
    G.crossingChangeCommutationHexagonWeight_eq_of_crossingCoveredSquares_eq R
      (D.commute_hexagon_crossingCoveredSquares h),
    D.commute_rectangle_toGridRectangle h, mul_comm]

open scoped Classical in
/-- The rectangle--hexagon and hexagon--rectangle domains with disjoint vertical sides counted by
the crossing change homotopy equation have the same total weight: reordering is a
weight-preserving bijection between them. -/
theorem sum_disjoint_crossingChangeRectangleHexagonWeight_eq
    (x z : GridState n) :
    ∑ D ∈ (G.crossingChangeRectangleHexagonDecompositions C t x z).filter
        (fun D => D.toRectangleDecomposition.HasDisjointSides),
      G.crossingChangeRectangleHexagonWeight C t R D =
    ∑ D ∈ (G.crossingChangeHexagonRectangleDecompositions C t x z).filter
        (fun D => D.toRectangleDecomposition.HasDisjointSides),
      G.crossingChangeHexagonRectangleWeight C t R D := by
  refine Finset.sum_bij'
    (fun D hD => D.commute (Finset.mem_filter.mp hD).2)
    (fun E hE => E.commute (Finset.mem_filter.mp hE).2) ?_ ?_ ?_ ?_ ?_
  · intro D hD
    obtain ⟨hD, h⟩ := Finset.mem_filter.mp hD
    exact Finset.mem_filter.mpr
      ⟨G.commute_mem_crossingChangeHexagonRectangleDecompositions C t D h hD,
        D.hasDisjointSides_commute h⟩
  · intro E hE
    obtain ⟨hE, h⟩ := Finset.mem_filter.mp hE
    exact Finset.mem_filter.mpr
      ⟨G.commute_mem_crossingChangeRectangleHexagonDecompositions C t E h hE,
        E.hasDisjointSides_commute h⟩
  · intro D hD
    exact D.commute_commute (Finset.mem_filter.mp hD).2
  · intro E hE
    exact E.commute_commute (Finset.mem_filter.mp hE).2
  · intro D hD
    exact (G.crossingChangeHexagonRectangleWeight_commute C t R D (Finset.mem_filter.mp hD).2).symm

open scoped Classical in
/-- In characteristic two, only the composite domains whose rectangles share a vertical side
contribute to the coefficients of `∂ ∘ H + H ∘ ∂`. -/
theorem sum_crossingChangeHexagonRectangleWeight_add_sum_eq_overlap
    [CharP R 2] (x z : GridState n) :
    (∑ D ∈ G.crossingChangeHexagonRectangleDecompositions C t x z,
        G.crossingChangeHexagonRectangleWeight C t R D) +
        ∑ D ∈ G.crossingChangeRectangleHexagonDecompositions C t x z,
          G.crossingChangeRectangleHexagonWeight C t R D =
      (∑ D ∈ (G.crossingChangeHexagonRectangleDecompositions C t x z).filter
          (fun D => ¬D.toRectangleDecomposition.HasDisjointSides),
        G.crossingChangeHexagonRectangleWeight C t R D) +
      ∑ D ∈ (G.crossingChangeRectangleHexagonDecompositions C t x z).filter
          (fun D => ¬D.toRectangleDecomposition.HasDisjointSides),
        G.crossingChangeRectangleHexagonWeight C t R D := by
  rw [← Finset.sum_filter_add_sum_filter_not
      (G.crossingChangeHexagonRectangleDecompositions C t x z)
      (fun D => D.toRectangleDecomposition.HasDisjointSides),
    ← Finset.sum_filter_add_sum_filter_not
      (G.crossingChangeRectangleHexagonDecompositions C t x z)
      (fun D => D.toRectangleDecomposition.HasDisjointSides),
    G.sum_disjoint_crossingChangeRectangleHexagonWeight_eq
      C t R x z,
    add_add_add_comm, CharTwo.add_self_eq_zero, zero_add]

end Disjoint

/-! ### The homotopy equation off the diagonal -/

section Equation

variable (C : ColumnTurn n) (t : Fin n) (R : Type*) [CommSemiring R]

local notation "a" => C.column
local notation "b" => finRotate n C.column

/-- The homotopy equation `∂H + H∂ = w + ΨΦ` of a crossing change, for a multiplier `w`, holds on
every chain exactly when it holds on every grid-state generator: all four maps are linear over the
polynomial ring. -/
private theorem unblockedDifferential_crossingChangeHomotopy_add_eq_iff_single
    (w : MvPolynomial (Fin n) R) :
    (∀ c : GridChainMinus R n,
      G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
          G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
        w • c + (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c)) ↔
      ∀ x : GridState n,
        G.unblockedDifferential R (G.crossingChangeHomotopy R C t (Finsupp.single x 1)) +
            G.crossingChangeHomotopy R C t (G.unblockedDifferential R (Finsupp.single x 1)) =
          Finsupp.single x w + (G.swapColumns a b).commutationMap R (C.withTurnRow t)
            (G.commutationMap R C (Finsupp.single x 1)) := by
  refine ⟨fun h x => by rw [h, Finsupp.smul_single_one], fun h c => ?_⟩
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero, add_zero, smul_zero]
  | add c d hc hd =>
    rw [map_add, map_add, map_add, map_add, map_add, add_add_add_comm, hc, hd, map_add,
      smul_add, add_add_add_comm]
  | single x p =>
    rw [← Finsupp.smul_single_one, map_smul, map_smul, map_smul, map_smul, ← smul_add, h,
      G.commutationMap_withTurnRow_commutationMap_smul R C t, smul_add, Finsupp.smul_single,
      smul_eq_mul, mul_comm, ← smul_eq_mul, ← Finsupp.smul_single, Finsupp.smul_single_one]

open scoped Classical in
/-- **The crossing change homotopy equation off the diagonal.** Let the turn rows `s` and `t`
differ and let the annulus squares carry no `X`-marking, and let `R` have characteristic two. Then
the homotopy equation `∂H + H∂ = w + ΨΦ`, with `w` the annulus weight, holds on every chain exactly
when, for all distinct grid states `x` and `z`, the counted composite domains from `x` to `z` whose
two rectangles share a vertical side have the total weight of the coefficient of `ΨΦ`, a sum over
pairs of pentagons. The diagonal coefficients always agree
(`GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_single_apply_self`), and the
composites with disjoint vertical sides cancel. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq_iff_overlap [CharP R 2]
    (hst : C.turnRow ≠ t) (hX : Disjoint (crossingChangeAnnulusSquares C t) G.XSet) :
    (∀ c : GridChainMinus R n,
      G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
          G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
        G.crossingChangeAnnulusWeight R C t • c +
          (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c)) ↔
      ∀ x z : GridState n, x ≠ z →
        (∑ D ∈ (G.crossingChangeHexagonRectangleDecompositions C t x z).filter
            (fun D => ¬D.toRectangleDecomposition.HasDisjointSides),
          G.crossingChangeHexagonRectangleWeight C t R D) +
          ∑ D ∈ (G.crossingChangeRectangleHexagonDecompositions C t x z).filter
              (fun D => ¬D.toRectangleDecomposition.HasDisjointSides),
            G.crossingChangeRectangleHexagonWeight C t R D =
          ∑ y : GridState n,
            MvPolynomial.rename (Equiv.swap a b) (G.commutationPentagonCoefficient R C x y) *
              (G.swapColumns a b).commutationPentagonCoefficient R (C.withTurnRow t) y z := by
  rw [unblockedDifferential_crossingChangeHomotopy_add_eq_iff_single]
  simp_rw [Finsupp.ext_iff, Finsupp.add_apply]
  refine forall_congr' fun x => ⟨fun h z hxz => ?_, fun h z => ?_⟩
  · have hz := h z
    rw [Finsupp.single_eq_of_ne' hxz, zero_add,
      unblockedDifferential_crossingChangeHomotopy_single_apply,
      crossingChangeHomotopy_unblockedDifferential_single_apply,
      sum_crossingChangeHexagonCoefficient_mul_unblockedCoefficient,
      sum_unblockedCoefficient_mul_crossingChangeHexagonCoefficient,
      sum_crossingChangeHexagonRectangleWeight_add_sum_eq_overlap,
      commutationMap_withTurnRow_commutationMap_single_apply] at hz
    exact hz
  · rcases eq_or_ne x z with rfl | hxz
    · rw [Finsupp.single_eq_same, ← Finsupp.add_apply]
      exact G.unblockedDifferential_crossingChangeHomotopy_add_single_apply_self R C t hst hX x
    · rw [Finsupp.single_eq_of_ne' hxz, zero_add,
        unblockedDifferential_crossingChangeHomotopy_single_apply,
        crossingChangeHomotopy_unblockedDifferential_single_apply,
        sum_crossingChangeHexagonCoefficient_mul_unblockedCoefficient,
        sum_unblockedCoefficient_mul_crossingChangeHexagonCoefficient,
        sum_crossingChangeHexagonRectangleWeight_add_sum_eq_overlap,
        commutationMap_withTurnRow_commutationMap_single_apply]
      exact h z hxz

end Equation

end GridDiagram

end TauCeti
