/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Basic
public import TauCeti.KnotTheory.Grid.Differential.Square.Decomposition
import TauCeti.KnotTheory.Grid.Commutation.Decomposition

/-!
# Rectangle--initial-side pentagon decompositions

The initial-side part of the commutation map contributes two-step domains in both orders:
a rectangle in the original diagram followed by a pentagon, or a pentagon followed by a
rectangle in the commuted diagram. Each is an ordinary rectangle decomposition with a
distinguished initial side and turn row. The pentagon is recovered from those constraints;
no additional domain data is carried.

The finite families below select empty, `X`-avoiding domains. Their weights use variables
of the commuted diagram: rename the original rectangle weight in the first order, and use
the commuted rectangle weight in the second. The two matrix products of the initial-side
pentagon map with the grid differentials are the weighted sums over these families.
Disjoint-side reordering identifies the two contributions; common-side domains require
separate recuts, sometimes involving terminal-side pentagons.

Two composite domains, one in each order, covering the same squares with the same multiplicities
have the same weight, once the rectangle of the commuted diagram is read in the original diagram
with the two commuted columns exchanged (`TauCeti.GridDiagram.
initialPentagonRectangleWeight_eq_rectangleInitialPentagonWeight_of_val_add_val_eq`).

The construction follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*,
Section 5.1, and the existing terminal-side decomposition API.

## Main results

* `TauCeti.GridDiagram.sum_rename_unblockedCoefficient_mul_initialPentagonCoefficient` and
  `TauCeti.GridDiagram.sum_initialPentagonCoefficient_mul_unblockedCoefficient_swapColumns`
  rewrite the two matrix products as sums over composite domains.
* `TauCeti.GridDiagram.initialPentagonMap_unblockedDifferential_single_apply` and
  `TauCeti.GridDiagram.unblockedDifferential_initialPentagonMap_single_apply`: the same
  identities for the coefficients of the two composites on a grid-state generator.
-/

public section

namespace TauCeti

/-- A rectangle followed by a pentagon turning on its initial side. -/
structure GridRectangleInitialPentagonDecomposition {n : ℕ} (a s : Fin n)
    (x z : GridState n) extends GridRectangleDecomposition x z where
  /-- The second domain starts on the replaced grid line. -/
  second_left_eq : second.left = finRotate n a
  /-- The turn row lies on the initial side of the second domain. -/
  second_turn_mem : s ∈ Grid.cIco second.bottom second.top

/-- A pentagon turning on its initial side followed by a rectangle. -/
structure GridInitialPentagonRectangleDecomposition {n : ℕ} (a s : Fin n)
    (x z : GridState n) extends GridRectangleDecomposition x z where
  /-- The first domain starts on the replaced grid line. -/
  first_left_eq : first.left = finRotate n a
  /-- The turn row lies on the initial side of the first domain. -/
  first_turn_mem : s ∈ Grid.cIco first.bottom first.top

namespace GridRectangleInitialPentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- Recover the initial-side pentagon from the second rectangle and its turn-point constraints. -/
def pentagon (D : GridRectangleInitialPentagonDecomposition a s x z) :
    GridInitialPentagonBetween a s D.middle z where
  toGridRectangleBetween := D.second
  left_eq := D.second_left_eq
  turn_mem := D.second_turn_mem

/-- Recovering the pentagon preserves its underlying oriented rectangle. -/
@[simp]
theorem pentagon_toGridRectangleBetween (D : GridRectangleInitialPentagonDecomposition a s x z) :
    D.pentagon.toGridRectangleBetween = D.second :=
  (rfl)

/-- The underlying rectangle decomposition determines all domain data. -/
theorem toGridRectangleDecomposition_injective : Function.Injective
    (toGridRectangleDecomposition : GridRectangleInitialPentagonDecomposition a s x z →
      GridRectangleDecomposition x z) := by
  rintro ⟨D, _, _⟩ ⟨E, _, _⟩ (rfl : D = E)
  rfl

/-- Equality of underlying rectangle decompositions is sufficient for equality. -/
@[ext]
theorem ext {D E : GridRectangleInitialPentagonDecomposition a s x z}
    (h : D.toGridRectangleDecomposition = E.toGridRectangleDecomposition) : D = E :=
  toGridRectangleDecomposition_injective h

/-- There are finitely many rectangle--initial-side pentagon decompositions. -/
noncomputable instance : Fintype (GridRectangleInitialPentagonDecomposition a s x z) :=
  Fintype.ofInjective _ ((GridRectangleDecomposition.sides_injective x z).comp
    toGridRectangleDecomposition_injective)

/-- A rectangle--initial-side pentagon decomposition is an intermediate state with a rectangle
into it and an initial-side pentagon out of it. -/
private def sigmaEquiv :
    (Σ y : GridState n, Σ _rectangle : GridRectangleBetween x y,
        GridInitialPentagonBetween a s y z) ≃
      GridRectangleInitialPentagonDecomposition a s x z where
  toFun D := ⟨⟨D.1, D.2.1, D.2.2.toGridRectangleBetween⟩, D.2.2.left_eq, D.2.2.turn_mem⟩
  invFun D := ⟨D.middle, D.first, D.pentagon⟩
  left_inv _ := rfl
  right_inv _ := rfl

end GridRectangleInitialPentagonDecomposition

namespace GridInitialPentagonRectangleDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

/-- Recover the initial-side pentagon from the first rectangle and its turn-point constraints. -/
def pentagon (D : GridInitialPentagonRectangleDecomposition a s x z) :
    GridInitialPentagonBetween a s x D.middle where
  toGridRectangleBetween := D.first
  left_eq := D.first_left_eq
  turn_mem := D.first_turn_mem

/-- Recovering the pentagon preserves its underlying oriented rectangle. -/
@[simp]
theorem pentagon_toGridRectangleBetween (D : GridInitialPentagonRectangleDecomposition a s x z) :
    D.pentagon.toGridRectangleBetween = D.first :=
  (rfl)

/-- The underlying rectangle decomposition determines all domain data. -/
theorem toGridRectangleDecomposition_injective : Function.Injective
    (toGridRectangleDecomposition : GridInitialPentagonRectangleDecomposition a s x z →
      GridRectangleDecomposition x z) := by
  rintro ⟨D, _, _⟩ ⟨E, _, _⟩ (rfl : D = E)
  rfl

/-- Equality of underlying rectangle decompositions is sufficient for equality. -/
@[ext]
theorem ext {D E : GridInitialPentagonRectangleDecomposition a s x z}
    (h : D.toGridRectangleDecomposition = E.toGridRectangleDecomposition) : D = E :=
  toGridRectangleDecomposition_injective h

/-- There are finitely many initial-side pentagon--rectangle decompositions. -/
noncomputable instance : Fintype (GridInitialPentagonRectangleDecomposition a s x z) :=
  Fintype.ofInjective _ ((GridRectangleDecomposition.sides_injective x z).comp
    toGridRectangleDecomposition_injective)

/-- An initial-side pentagon--rectangle decomposition is an intermediate state with an
initial-side pentagon into it and a rectangle out of it. -/
private def sigmaEquiv :
    (Σ y : GridState n, Σ _pentagon : GridInitialPentagonBetween a s x y,
        GridRectangleBetween y z) ≃
      GridInitialPentagonRectangleDecomposition a s x z where
  toFun D := ⟨⟨D.1, D.2.1.toGridRectangleBetween, D.2.2⟩, D.2.1.left_eq, D.2.1.turn_mem⟩
  invFun D := ⟨D.middle, D.pentagon, D.second⟩
  left_inv _ := rfl
  right_inv _ := rfl

end GridInitialPentagonRectangleDecomposition

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n) (C : ColumnCommutationData G)

/-- The counted rectangle--initial-side pentagon domains: a rectangle of the original diagram
and an initial-side pentagon counted by the commutation map. -/
noncomputable def rectangleInitialPentagonDecompositions (x z : GridState n) :
    Finset (GridRectangleInitialPentagonDecomposition C.column C.turnRow x z) := by
  classical
  exact Finset.univ.filter fun D =>
    D.first ∈ G.unblockedRectangles x D.middle ∧
      D.pentagon ∈ G.initialPentagons C D.middle z

/-- Membership means that both constituent domains are counted. -/
@[simp]
theorem mem_rectangleInitialPentagonDecompositions {x z : GridState n}
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z) :
    D ∈ G.rectangleInitialPentagonDecompositions C x z ↔
      D.first ∈ G.unblockedRectangles x D.middle ∧
        D.pentagon ∈ G.initialPentagons C D.middle z := by
  classical
  simp [rectangleInitialPentagonDecompositions]

/-- The counted initial-side pentagon--rectangle domains: an initial-side pentagon counted by
the commutation map and a rectangle of the commuted diagram. -/
noncomputable def initialPentagonRectangleDecompositions (x z : GridState n) :
    Finset (GridInitialPentagonRectangleDecomposition C.column C.turnRow x z) := by
  classical
  exact Finset.univ.filter fun D =>
    D.pentagon ∈ G.initialPentagons C x D.middle ∧
      D.second ∈ (G.swapColumns C.column (finRotate n C.column)).unblockedRectangles D.middle z

/-- Membership means that both constituent domains are counted. -/
@[simp]
theorem mem_initialPentagonRectangleDecompositions {x z : GridState n}
    (D : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z) :
    D ∈ G.initialPentagonRectangleDecompositions C x z ↔
      D.pentagon ∈ G.initialPentagons C x D.middle ∧
        D.second ∈
          (G.swapColumns C.column (finRotate n C.column)).unblockedRectangles D.middle z := by
  classical
  simp [initialPentagonRectangleDecompositions]

variable (R : Type*) [CommSemiring R]

/-- The weight of a rectangle followed by an initial-side pentagon, in the variables of the
commuted diagram. -/
noncomputable def rectangleInitialPentagonWeight {x z : GridState n}
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z) :
    MvPolynomial (Fin n) R :=
  MvPolynomial.rename (Equiv.swap C.column (finRotate n C.column))
    (G.OMonomial R D.first.toGridRectangle) * G.initialPentagonWeight R C D.pentagon

/-- The composite weight is the renamed rectangle weight times the pentagon weight. -/
theorem rectangleInitialPentagonWeight_def {x z : GridState n}
    (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z) :
    G.rectangleInitialPentagonWeight C R D =
      MvPolynomial.rename (Equiv.swap C.column (finRotate n C.column))
        (G.OMonomial R D.first.toGridRectangle) * G.initialPentagonWeight R C D.pentagon :=
  (rfl)

/-- The weight of an initial-side pentagon followed by a rectangle of the commuted diagram. -/
noncomputable def initialPentagonRectangleWeight {x z : GridState n}
    (D : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z) :
    MvPolynomial (Fin n) R :=
  G.initialPentagonWeight R C D.pentagon *
    (G.swapColumns C.column (finRotate n C.column)).OMonomial R D.second.toGridRectangle

/-- The composite weight is the pentagon weight times the commuted rectangle weight. -/
theorem initialPentagonRectangleWeight_def {x z : GridState n}
    (D : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z) :
    G.initialPentagonRectangleWeight C R D =
      G.initialPentagonWeight R C D.pentagon *
        (G.swapColumns C.column (finRotate n C.column)).OMonomial R D.second.toGridRectangle :=
  (rfl)

/-- An initial-side pentagon followed by a rectangle of the commuted diagram has the weight of a
rectangle followed by an initial-side pentagon when the two composite domains cover the same
squares with the same multiplicities, the squares of the rectangle of the commuted diagram being
read in the original diagram, that is with the two commuted columns exchanged. -/
theorem initialPentagonRectangleWeight_eq_rectangleInitialPentagonWeight_of_val_add_val_eq
    {x z : GridState n} (D : GridRectangleInitialPentagonDecomposition C.column C.turnRow x z)
    (E : GridInitialPentagonRectangleDecomposition C.column C.turnRow x z)
    (h : E.pentagon.coveredSquares.val +
        (E.second.toGridRectangle.coveredSquares.map
          ((Equiv.swap C.column (finRotate n C.column)).prodCongr
            (Equiv.refl (Fin n))).toEmbedding).val =
      D.first.toGridRectangle.coveredSquares.val + D.pentagon.coveredSquares.val) :
    G.initialPentagonRectangleWeight C R E = G.rectangleInitialPentagonWeight C R D := by
  rw [initialPentagonRectangleWeight_def, rectangleInitialPentagonWeight_def,
    initialPentagonWeight_eq_prod_coveredSquares, initialPentagonWeight_eq_prod_coveredSquares,
    OMonomial_swapColumns_eq_prod_swapSquareWeight, rename_OMonomial_eq_prod_swapSquareWeight]
  simp only [← swapSquareWeight_def, Finset.prod_eq_multiset_prod, ← Multiset.prod_add,
    ← Multiset.map_add, h]

/-- The matrix product for the initial-side pentagon map after the original differential is the
sum of the weights of the counted rectangle--initial-side pentagon decompositions. -/
theorem sum_rename_unblockedCoefficient_mul_initialPentagonCoefficient (x z : GridState n) :
    ∑ y : GridState n,
        MvPolynomial.rename (Equiv.swap C.column (finRotate n C.column))
            (G.unblockedCoefficient R x y) *
          G.initialPentagonCoefficient R C y z =
      ∑ D ∈ G.rectangleInitialPentagonDecompositions C x z,
        G.rectangleInitialPentagonWeight C R D := by
  classical
  simp_rw [G.unblockedCoefficient_def R x, map_sum, G.initialPentagonCoefficient_def R C,
    Finset.sum_mul_sum, Finset.sum_sigma']
  -- `sigmaEquiv` repackages its components, so its projections are definitionally them.
  refine Finset.sum_equiv GridRectangleInitialPentagonDecomposition.sigmaEquiv
    (fun D => ?_) fun D _ => rfl
  simp only [Finset.mem_sigma, Finset.mem_univ, true_and,
    mem_rectangleInitialPentagonDecompositions]
  exact Iff.rfl

/-- The matrix product for the commuted differential after the initial-side pentagon map is the
sum of the weights of the counted initial-side pentagon--rectangle decompositions. -/
theorem sum_initialPentagonCoefficient_mul_unblockedCoefficient_swapColumns (x z : GridState n) :
    ∑ y : GridState n, G.initialPentagonCoefficient R C x y *
        (G.swapColumns C.column (finRotate n C.column)).unblockedCoefficient R y z =
      ∑ D ∈ G.initialPentagonRectangleDecompositions C x z,
        G.initialPentagonRectangleWeight C R D := by
  classical
  simp_rw [G.initialPentagonCoefficient_def R C x,
    (G.swapColumns C.column (finRotate n C.column)).unblockedCoefficient_def R _ z,
    Finset.sum_mul_sum, Finset.sum_sigma']
  -- `sigmaEquiv` repackages its components, so its projections are definitionally them.
  refine Finset.sum_equiv GridInitialPentagonRectangleDecomposition.sigmaEquiv
    (fun D => ?_) fun D _ => rfl
  simp only [Finset.mem_sigma, Finset.mem_univ, true_and,
    mem_initialPentagonRectangleDecompositions]
  exact Iff.rfl

/-- On a grid-state generator, the coefficient of the initial-side pentagon map after the
original differential is the rectangle--initial-side pentagon decomposition sum. -/
theorem initialPentagonMap_unblockedDifferential_single_apply (x z : GridState n) :
    G.initialPentagonMap R C (G.unblockedDifferential R (Finsupp.single x 1)) z =
      ∑ D ∈ G.rectangleInitialPentagonDecompositions C x z,
        G.rectangleInitialPentagonWeight C R D := by
  rw [G.initialPentagonMap_apply_apply R C, G.unblockedDifferential_single,
    Finsupp.sum_fintype _ _ fun _ => by simp]
  simp_rw [G.unblockedDifferentialOnGenerator_apply R x]
  exact G.sum_rename_unblockedCoefficient_mul_initialPentagonCoefficient C R x z

/-- On a grid-state generator, the coefficient of the commuted differential after the
initial-side pentagon map is the initial-side pentagon--rectangle decomposition sum. -/
theorem unblockedDifferential_initialPentagonMap_single_apply (x z : GridState n) :
    (G.swapColumns C.column (finRotate n C.column)).unblockedDifferential R
        (G.initialPentagonMap R C (Finsupp.single x 1)) z =
      ∑ D ∈ G.initialPentagonRectangleDecompositions C x z,
        G.initialPentagonRectangleWeight C R D := by
  rw [(G.swapColumns C.column (finRotate n C.column)).unblockedDifferential_apply_apply R,
    Finsupp.sum_fintype _ _ fun _ => zero_mul _]
  simp only [G.initialPentagonMap_apply_apply R C, map_zero, zero_mul, Finsupp.sum_single_index,
    map_one, one_mul]
  exact G.sum_initialPentagonCoefficient_mul_unblockedCoefficient_swapColumns C R x z

end GridDiagram

end TauCeti
