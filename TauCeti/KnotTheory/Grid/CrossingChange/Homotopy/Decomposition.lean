/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.CrossingChange.Homotopy.Diagonal
public import TauCeti.KnotTheory.Grid.Commutation.Homotopy.Decomposition

/-!
# Composite domains in the crossing change homotopy equation

Let `C` be a column turn at the columns `a` and `b = finRotate n a` of a grid diagram `G`, turning
in row `s`, and let `t` be a second row. Write `Φ : GC⁻(G) → GC⁻(G')` for the commutation map of
`C`, where `G' = G.swapColumns a b`, `Ψ : GC⁻(G') → GC⁻(G)` for the commutation map of `G'` at
`C.withTurnRow t`, and `H : GC⁻(G) → GC⁻(G)` for the crossing change homotopy
`GridDiagram.crossingChangeHomotopy` with corners in the rows `s` and `t`. For interleaving
columns, with `s` and `t` the rows of the turn points of the crossing change maps, the homotopy
equation of Ozsváth--Stipsicz--Szabó, Section 6.1, reads

  `∂ ∘ H + H ∘ ∂ = V + Ψ ∘ Φ`

over `𝔽₂`, for the variable `V` of one of the two columns.

This file writes that equation, with an arbitrary polynomial `w` in place of `V`, as an identity
of matrix coefficients, and rewrites its left-hand side as sums over the two-step domains it
counts: a counted hexagon followed by an empty rectangle carrying no `X`-marking, and the same in
the other order. The two hexagon shapes counted by `H` are combined, as for the commutation
homotopy, into the sum type `TauCeti.GridCommutationHexagonBetween`, and the composite domains are
the generic `TauCeti.GridHexagonRectangleDecomposition` and
`TauCeti.GridRectangleHexagonDecomposition`.
Only the markings a crossing-change hexagon carries differ from those of a commutation hexagon:
they are its `crossingCoveredSquares`.

## Main definitions

* `TauCeti.GridCommutationHexagonBetween.crossingCoveredSquares`: the squares whose markings lie
  inside a hexagon of either shape, read as a hexagon of a crossing change.
* `TauCeti.GridDiagram.crossingChangeCommutationHexagons` and
  `TauCeti.GridDiagram.crossingChangeCommutationHexagonWeight`: the counted hexagons of both
  shapes, and their weights.
* `TauCeti.GridDiagram.crossingChangeHexagonRectangleDecompositions` and
  `TauCeti.GridDiagram.crossingChangeRectangleHexagonDecompositions`, with weights
  `TauCeti.GridDiagram.crossingChangeHexagonRectangleWeight` and
  `TauCeti.GridDiagram.crossingChangeRectangleHexagonWeight`: the composite domains counted by
  `∂ ∘ H` and `H ∘ ∂`.
* `TauCeti.GridDiagram.crossingChangeHexagonCompositeDecompositions` and
  `TauCeti.GridDiagram.crossingChangeHexagonCompositeWeight`: the counted composites of both
  orders, as one family of `TauCeti.GridHexagonCompositeDecomposition`, and their weights.

## Main results

* `TauCeti.GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_iff`: the equation
  `∂ ∘ H + H ∘ ∂ = w + Ψ ∘ Φ` holds on every chain exactly when it holds on the matrix
  coefficients between grid states.
* `TauCeti.GridDiagram.unblockedDifferential_crossingChangeHomotopy_add_eq_iff_decompositions`:
  the same, with the left-hand side written as sums over the counted composite domains.

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

/-- The squares whose markings lie inside a hexagon of either shape, read as a hexagon of a
crossing change: the `crossingCoveredSquares` of the hexagon turning on its terminal or on its
initial side. -/
noncomputable def crossingCoveredSquares (P : GridCommutationHexagonBetween a s s' x y) :
    Finset (Fin n × Fin n) :=
  P.elim GridHexagonBetween.crossingCoveredSquares GridInitialHexagonBetween.crossingCoveredSquares

/-- The crossing-change squares of a hexagon turning on its terminal side. -/
@[simp]
theorem crossingCoveredSquares_inl (P : GridHexagonBetween a s' s x y) :
    crossingCoveredSquares (Sum.inl P : GridCommutationHexagonBetween a s s' x y) =
      P.crossingCoveredSquares := (rfl)

/-- The crossing-change squares of a hexagon turning on its initial side. -/
@[simp]
theorem crossingCoveredSquares_inr (P : GridInitialHexagonBetween a s s' x y) :
    crossingCoveredSquares (Sum.inr P : GridCommutationHexagonBetween a s s' x y) =
      P.crossingCoveredSquares := (rfl)

/-- The squares covered by a hexagon of either shape, read as a hexagon of a crossing change,
depend only on its underlying toroidal rectangle. -/
theorem crossingCoveredSquares_eq_of_toGridRectangle_eq {u v : GridState n}
    (P : GridCommutationHexagonBetween a s s' x y) (Q : GridCommutationHexagonBetween a s s' u v)
    (h : P.toGridRectangleBetween.toGridRectangle = Q.toGridRectangleBetween.toGridRectangle) :
    P.crossingCoveredSquares = Q.crossingCoveredSquares := by
  -- Hexagons of the two shapes have different left sides, so the shape is determined as well.
  have hl := congrArg GridRectangle.left h
  cases P <;> cases Q <;>
    simp only [toGridRectangleBetween_inl, toGridRectangleBetween_inr,
      GridRectangleBetween.toGridRectangle_left] at h hl
  · exact GridHexagonBetween.crossingCoveredSquares_eq_of_toGridRectangle_eq _ _ h
  · exact absurd (hl.trans (by assumption : GridInitialHexagonBetween a s s' u v).left_eq)
      (by assumption : GridHexagonBetween a s' s x y).left_ne
  · exact absurd (hl.symm.trans (by assumption : GridInitialHexagonBetween a s s' x y).left_eq)
      (by assumption : GridHexagonBetween a s' s u v).left_ne
  · exact GridInitialHexagonBetween.crossingCoveredSquares_eq_of_toGridRectangle_eq _ _ h

/-- Transferring a hexagon along an equality of underlying toroidal rectangles preserves the
squares it covers as a hexagon of a crossing change. -/
@[simp]
theorem ofToGridRectangleEq_crossingCoveredSquares {u v : GridState n}
    (r : GridRectangleBetween u v) (P : GridCommutationHexagonBetween a s s' x y)
    (h : r.toGridRectangle = P.toGridRectangleBetween.toGridRectangle) :
    (ofToGridRectangleEq r P h).crossingCoveredSquares = P.crossingCoveredSquares :=
  crossingCoveredSquares_eq_of_toGridRectangle_eq _ _
    ((congrArg GridRectangleBetween.toGridRectangle
      (ofToGridRectangleEq_toGridRectangleBetween r P h)).trans h)

end GridCommutationHexagonBetween

namespace GridDiagram

open MvPolynomial

variable {n : ℕ} (G : GridDiagram n) (C : ColumnTurn n) (t : Fin n)

local notation "a" => C.column
local notation "b" => finRotate n C.column

/-! ### The counted hexagons of both shapes -/

/-- The hexagons counted by the crossing change homotopy from `x` to `y`, of both shapes: the
counted hexagons turning on their terminal side and those turning on their initial side. -/
noncomputable def crossingChangeCommutationHexagons (x y : GridState n) :
    Finset (GridCommutationHexagonBetween a C.turnRow t x y) :=
  (G.crossingChangeHexagons C t x y).disjSum (G.crossingChangeInitialHexagons C t x y)

/-- A hexagon of either shape is counted by the crossing change homotopy exactly when its
underlying rectangle is empty and the squares it covers as a hexagon of a crossing change avoid
every `X`-marking. -/
@[simp]
theorem mem_crossingChangeCommutationHexagons {x y : GridState n}
    (P : GridCommutationHexagonBetween a C.turnRow t x y) :
    P ∈ G.crossingChangeCommutationHexagons C t x y ↔
      P.toGridRectangleBetween.IsEmpty ∧ Disjoint P.crossingCoveredSquares G.XSet := by
  cases P <;> simp [crossingChangeCommutationHexagons]

variable (R : Type*) [CommSemiring R]

/-- The weight of a crossing-change hexagon of either shape: the product of the variables of the
`O`-markings it carries. -/
noncomputable def crossingChangeCommutationHexagonWeight {x y : GridState n}
    (P : GridCommutationHexagonBetween a C.turnRow t x y) : MvPolynomial (Fin n) R :=
  P.elim (G.crossingChangeHexagonWeight R) (G.crossingChangeInitialHexagonWeight R)

/-- The weight of a crossing-change hexagon turning on its terminal side. -/
@[simp]
theorem crossingChangeCommutationHexagonWeight_inl {x y : GridState n}
    (P : GridHexagonBetween a t C.turnRow x y) :
    G.crossingChangeCommutationHexagonWeight C t R (Sum.inl P) =
      G.crossingChangeHexagonWeight R P := (rfl)

/-- The weight of a crossing-change hexagon turning on its initial side. -/
@[simp]
theorem crossingChangeCommutationHexagonWeight_inr {x y : GridState n}
    (P : GridInitialHexagonBetween a C.turnRow t x y) :
    G.crossingChangeCommutationHexagonWeight C t R (Sum.inr P) =
      G.crossingChangeInitialHexagonWeight R P := (rfl)

/-- The weight of a crossing-change hexagon of either shape is the squarefree monomial of the
`O`-markings in the squares it covers as a hexagon of a crossing change. -/
theorem crossingChangeCommutationHexagonWeight_eq_monomial {x y : GridState n}
    (P : GridCommutationHexagonBetween a C.turnRow t x y) :
    G.crossingChangeCommutationHexagonWeight C t R P =
      monomial (∑ c ∈ G.OColumnsOfSquares P.crossingCoveredSquares, Finsupp.single c 1) 1 := by
  cases P with
  | inl P => exact G.crossingChangeHexagonWeight_eq_monomial R P
  | inr P => exact G.crossingChangeInitialHexagonWeight_eq_monomial R P

/-- The weight of a crossing-change hexagon of either shape is the product of the variables of the
columns of the `O`-markings in the squares it covers as a hexagon of a crossing change. -/
theorem crossingChangeCommutationHexagonWeight_eq_prod_crossingCoveredSquares {x y : GridState n}
    (P : GridCommutationHexagonBetween a C.turnRow t x y) :
    G.crossingChangeCommutationHexagonWeight C t R P =
      ∏ c ∈ G.OColumnsOfSquares P.crossingCoveredSquares, MvPolynomial.X c := by
  rw [crossingChangeCommutationHexagonWeight_eq_monomial, monomial_sum_one]
  simp only [← X_pow_eq_monomial, pow_one]

/-- The matrix coefficient of the crossing change homotopy is the sum of the weights of the
counted hexagons of both shapes. -/
theorem crossingChangeHexagonCoefficient_eq_sum_weight (x y : GridState n) :
    G.crossingChangeHexagonCoefficient R C t x y =
      ∑ P ∈ G.crossingChangeCommutationHexagons C t x y,
        G.crossingChangeCommutationHexagonWeight C t R P := by
  rw [crossingChangeHexagonCoefficient_def, crossingChangeCommutationHexagons, Finset.sum_disjSum]
  simp only [crossingChangeCommutationHexagonWeight_inl, crossingChangeCommutationHexagonWeight_inr]

/-! ### The counted composite domains -/

/-- The composite domains counted in the coefficients of the unblocked differential after the
crossing change homotopy: a counted hexagon of either shape followed by a counted rectangle. -/
noncomputable def crossingChangeHexagonRectangleDecompositions (x z : GridState n) :
    Finset (GridHexagonRectangleDecomposition a C.turnRow t x z) :=
  GridTwoStepDecomposition.decompositionsOf (G.crossingChangeCommutationHexagons C t)
    G.unblockedRectangles x z

/-- Membership in the counted hexagon--rectangle family is countedness of both domains. -/
@[simp]
theorem mem_crossingChangeHexagonRectangleDecompositions {x z : GridState n}
    (D : GridHexagonRectangleDecomposition a C.turnRow t x z) :
    D ∈ G.crossingChangeHexagonRectangleDecompositions C t x z ↔
      D.hexagon ∈ G.crossingChangeCommutationHexagons C t x D.middle ∧
        D.rectangle ∈ G.unblockedRectangles D.middle z := by
  classical
  simp only [crossingChangeHexagonRectangleDecompositions,
    GridTwoStepDecomposition.mem_decompositionsOf]

/-- The composite domains counted in the coefficients of the crossing change homotopy after the
unblocked differential: a counted rectangle followed by a counted hexagon of either shape. -/
noncomputable def crossingChangeRectangleHexagonDecompositions (x z : GridState n) :
    Finset (GridRectangleHexagonDecomposition a C.turnRow t x z) :=
  GridTwoStepDecomposition.decompositionsOf G.unblockedRectangles
    (G.crossingChangeCommutationHexagons C t) x z

/-- Membership in the counted rectangle--hexagon family is countedness of both domains. -/
@[simp]
theorem mem_crossingChangeRectangleHexagonDecompositions {x z : GridState n}
    (D : GridRectangleHexagonDecomposition a C.turnRow t x z) :
    D ∈ G.crossingChangeRectangleHexagonDecompositions C t x z ↔
      D.rectangle ∈ G.unblockedRectangles x D.middle ∧
        D.hexagon ∈ G.crossingChangeCommutationHexagons C t D.middle z := by
  classical
  simp only [crossingChangeRectangleHexagonDecompositions,
    GridTwoStepDecomposition.mem_decompositionsOf]

/-- The weight of a crossing-change hexagon followed by a rectangle: the product of the two domain
weights. -/
noncomputable def crossingChangeHexagonRectangleWeight {x z : GridState n}
    (D : GridHexagonRectangleDecomposition a C.turnRow t x z) : MvPolynomial (Fin n) R :=
  G.crossingChangeCommutationHexagonWeight C t R D.hexagon *
    G.OMonomial R D.rectangle.toGridRectangle

/-- The weight of a hexagon--rectangle decomposition is the product of the two domain weights. -/
theorem crossingChangeHexagonRectangleWeight_def {x z : GridState n}
    (D : GridHexagonRectangleDecomposition a C.turnRow t x z) :
    G.crossingChangeHexagonRectangleWeight C t R D =
      G.crossingChangeCommutationHexagonWeight C t R D.hexagon *
        G.OMonomial R D.rectangle.toGridRectangle := (rfl)

/-- The weight of a rectangle followed by a crossing-change hexagon: the product of the two domain
weights. -/
noncomputable def crossingChangeRectangleHexagonWeight {x z : GridState n}
    (D : GridRectangleHexagonDecomposition a C.turnRow t x z) : MvPolynomial (Fin n) R :=
  G.OMonomial R D.rectangle.toGridRectangle *
    G.crossingChangeCommutationHexagonWeight C t R D.hexagon

/-- The weight of a rectangle--hexagon decomposition is the product of the two domain weights. -/
theorem crossingChangeRectangleHexagonWeight_def {x z : GridState n}
    (D : GridRectangleHexagonDecomposition a C.turnRow t x z) :
    G.crossingChangeRectangleHexagonWeight C t R D =
      G.OMonomial R D.rectangle.toGridRectangle *
        G.crossingChangeCommutationHexagonWeight C t R D.hexagon := (rfl)

/-! ### The counted composites of both orders -/

/-- The counted composites from `x` to `z`: the counted hexagon--rectangle and rectangle--hexagon
decompositions of the crossing change homotopy equation. -/
noncomputable def crossingChangeHexagonCompositeDecompositions (x z : GridState n) :
    Finset (GridHexagonCompositeDecomposition a C.turnRow t x z) :=
  (G.crossingChangeHexagonRectangleDecompositions C t x z).disjSum
    (G.crossingChangeRectangleHexagonDecompositions C t x z)

/-- The counted composites are the disjoint union of the counted hexagon--rectangle and
rectangle--hexagon decompositions. -/
theorem crossingChangeHexagonCompositeDecompositions_def (x z : GridState n) :
    G.crossingChangeHexagonCompositeDecompositions C t x z =
      (G.crossingChangeHexagonRectangleDecompositions C t x z).disjSum
        (G.crossingChangeRectangleHexagonDecompositions C t x z) := (rfl)

/-- A hexagon followed by a rectangle is a counted composite exactly when it is counted as a
hexagon--rectangle decomposition. -/
@[simp]
theorem inl_mem_crossingChangeHexagonCompositeDecompositions {x z : GridState n}
    (D : GridHexagonRectangleDecomposition a C.turnRow t x z) :
    Sum.inl D ∈ G.crossingChangeHexagonCompositeDecompositions C t x z ↔
      D ∈ G.crossingChangeHexagonRectangleDecompositions C t x z :=
  Finset.inl_mem_disjSum

/-- A rectangle followed by a hexagon is a counted composite exactly when it is counted as a
rectangle--hexagon decomposition. -/
@[simp]
theorem inr_mem_crossingChangeHexagonCompositeDecompositions {x z : GridState n}
    (D : GridRectangleHexagonDecomposition a C.turnRow t x z) :
    Sum.inr D ∈ G.crossingChangeHexagonCompositeDecompositions C t x z ↔
      D ∈ G.crossingChangeRectangleHexagonDecompositions C t x z :=
  Finset.inr_mem_disjSum

/-- The weight of a composite of the crossing change homotopy equation: that of its
hexagon--rectangle or rectangle--hexagon decomposition. -/
noncomputable def crossingChangeHexagonCompositeWeight {x z : GridState n}
    (D : GridHexagonCompositeDecomposition a C.turnRow t x z) : MvPolynomial (Fin n) R :=
  D.elim (G.crossingChangeHexagonRectangleWeight C t R)
    (G.crossingChangeRectangleHexagonWeight C t R)

/-- The weight of a hexagon followed by a rectangle. -/
@[simp]
theorem crossingChangeHexagonCompositeWeight_inl {x z : GridState n}
    (D : GridHexagonRectangleDecomposition a C.turnRow t x z) :
    G.crossingChangeHexagonCompositeWeight C t R (Sum.inl D) =
      G.crossingChangeHexagonRectangleWeight C t R D := (rfl)

/-- The weight of a rectangle followed by a hexagon. -/
@[simp]
theorem crossingChangeHexagonCompositeWeight_inr {x z : GridState n}
    (D : GridRectangleHexagonDecomposition a C.turnRow t x z) :
    G.crossingChangeHexagonCompositeWeight C t R (Sum.inr D) =
      G.crossingChangeRectangleHexagonWeight C t R D := (rfl)

variable {G C t}

/-- Both rectangles under a counted composite are empty. -/
theorem isEmpty_of_mem_crossingChangeHexagonCompositeDecompositions {x z : GridState n}
    {D : GridHexagonCompositeDecomposition a C.turnRow t x z}
    (hD : D ∈ G.crossingChangeHexagonCompositeDecompositions C t x z) :
    D.toRectangleDecomposition.first.IsEmpty ∧ D.toRectangleDecomposition.second.IsEmpty := by
  cases D with
  | inl D =>
    obtain ⟨hP, hr⟩ := (G.mem_crossingChangeHexagonRectangleDecompositions C t D).mp
      ((G.inl_mem_crossingChangeHexagonCompositeDecompositions C t D).mp hD)
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inl]
    exact ⟨((G.mem_crossingChangeCommutationHexagons C t _).mp hP).1,
      G.isEmpty_of_mem_unblockedRectangles hr⟩
  | inr D =>
    obtain ⟨hr, hP⟩ := (G.mem_crossingChangeRectangleHexagonDecompositions C t D).mp
      ((G.inr_mem_crossingChangeHexagonCompositeDecompositions C t D).mp hD)
    rw [GridHexagonCompositeDecomposition.toRectangleDecomposition_inr]
    exact ⟨G.isEmpty_of_mem_unblockedRectangles hr,
      ((G.mem_crossingChangeCommutationHexagons C t _).mp hP).1⟩

variable (G C t)

/-- The hexagon--rectangle matrix product of the crossing change homotopy is the sum of the
weights of the counted composite domains. -/
theorem sum_crossingChangeHexagonCoefficient_mul_unblockedCoefficient (x z : GridState n) :
    ∑ y : GridState n,
        G.crossingChangeHexagonCoefficient R C t x y * G.unblockedCoefficient R y z =
      ∑ D ∈ G.crossingChangeHexagonRectangleDecompositions C t x z,
        G.crossingChangeHexagonRectangleWeight C t R D := by
  simp_rw [G.crossingChangeHexagonCoefficient_eq_sum_weight C t R, G.unblockedCoefficient_def R,
    Finset.sum_mul_sum]
  exact (GridTwoStepDecomposition.sum_decompositionsOf
    (G.crossingChangeCommutationHexagons C t) G.unblockedRectangles
    (fun _ P r => G.crossingChangeCommutationHexagonWeight C t R P *
      G.OMonomial R r.toGridRectangle)).symm

/-- The rectangle--hexagon matrix product of the crossing change homotopy is the sum of the
weights of the counted composite domains. -/
theorem sum_unblockedCoefficient_mul_crossingChangeHexagonCoefficient (x z : GridState n) :
    ∑ y : GridState n,
        G.unblockedCoefficient R x y * G.crossingChangeHexagonCoefficient R C t y z =
      ∑ D ∈ G.crossingChangeRectangleHexagonDecompositions C t x z,
        G.crossingChangeRectangleHexagonWeight C t R D := by
  simp_rw [G.unblockedCoefficient_def R, G.crossingChangeHexagonCoefficient_eq_sum_weight C t R,
    Finset.sum_mul_sum]
  exact (GridTwoStepDecomposition.sum_decompositionsOf G.unblockedRectangles
    (G.crossingChangeCommutationHexagons C t)
    (fun _ r P => G.OMonomial R r.toGridRectangle *
      G.crossingChangeCommutationHexagonWeight C t R P)).symm

/-! ### The homotopy equation as a coefficient identity -/

/-- The equation `∂ ∘ H + H ∘ ∂ = w + Ψ ∘ Φ` for the crossing change homotopy `H`, the
commutation map `Φ` of `C` and the commutation map `Ψ` of the commuted diagram turning in row `t`
holds on every chain exactly when, for all grid states `x` and `z`, the products of hexagon and
rectangle coefficients through intermediate states, in both orders, sum to `w` times the Kronecker
delta of `x` and `z` plus the products of the coefficients of `Φ`, renamed by the column swap, and
of `Ψ`. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq_iff (w : MvPolynomial (Fin n) R) :
    (∀ c : GridChainMinus R n,
      G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
          G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
        w • c + (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c)) ↔
      ∀ x z : GridState n,
        ∑ y : GridState n,
            (G.crossingChangeHexagonCoefficient R C t x y * G.unblockedCoefficient R y z +
              G.unblockedCoefficient R x y * G.crossingChangeHexagonCoefficient R C t y z) =
          (if x = z then w else 0) +
            ∑ y : GridState n,
              rename (Equiv.swap a b) (G.commutationPentagonCoefficient R C x y) *
                (G.swapColumns a b).commutationPentagonCoefficient R (C.withTurnRow t) y z := by
  have hw (x z : GridState n) :
      (if x = z then w else 0) = (w • Finsupp.single x (1 : MvPolynomial (Fin n) R)) z := by
    rw [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp_rw [Finset.sum_add_distrib, ← unblockedDifferential_crossingChangeHomotopy_single_apply,
    ← crossingChangeHomotopy_unblockedDifferential_single_apply,
    ← commutationMap_withTurnRow_commutationMap_single_apply, hw, ← Finsupp.add_apply,
    ← Finsupp.ext_iff]
  refine ⟨fun h x => h _, fun h c => ?_⟩
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero, add_zero, smul_zero]
  | add c d hc hd =>
    rw [map_add, map_add, map_add, map_add, map_add, add_add_add_comm, hc, hd, map_add, smul_add,
      add_add_add_comm]
  | single x p =>
    rw [← Finsupp.smul_single_one, map_smul, map_smul, map_smul, map_smul, ← smul_add, h,
      commutationMap_withTurnRow_commutationMap_smul, smul_add, smul_comm p w]

/-- The crossing change homotopy equation `∂ ∘ H + H ∘ ∂ = w + Ψ ∘ Φ` holds on every chain exactly
when, for all grid states `x` and `z`, the counted hexagon--rectangle and rectangle--hexagon
domains from `x` to `z` have total weight `w` times the Kronecker delta of `x` and `z` plus the
products of the coefficients of `Φ`, renamed by the column swap, and of `Ψ`. -/
theorem unblockedDifferential_crossingChangeHomotopy_add_eq_iff_decompositions
    (w : MvPolynomial (Fin n) R) :
    (∀ c : GridChainMinus R n,
      G.unblockedDifferential R (G.crossingChangeHomotopy R C t c) +
          G.crossingChangeHomotopy R C t (G.unblockedDifferential R c) =
        w • c + (G.swapColumns a b).commutationMap R (C.withTurnRow t) (G.commutationMap R C c)) ↔
      ∀ x z : GridState n,
        (∑ D ∈ G.crossingChangeHexagonRectangleDecompositions C t x z,
            G.crossingChangeHexagonRectangleWeight C t R D) +
            ∑ D ∈ G.crossingChangeRectangleHexagonDecompositions C t x z,
              G.crossingChangeRectangleHexagonWeight C t R D =
          (if x = z then w else 0) +
            ∑ y : GridState n,
              rename (Equiv.swap a b) (G.commutationPentagonCoefficient R C x y) *
                (G.swapColumns a b).commutationPentagonCoefficient R (C.withTurnRow t) y z := by
  rw [G.unblockedDifferential_crossingChangeHomotopy_add_eq_iff C t R w]
  simp_rw [Finset.sum_add_distrib,
    G.sum_crossingChangeHexagonCoefficient_mul_unblockedCoefficient C t R,
    G.sum_unblockedCoefficient_mul_crossingChangeHexagonCoefficient C t R]

end GridDiagram

end TauCeti
