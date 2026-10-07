/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Commutation.InitialPentagon.Basic
public import TauCeti.KnotTheory.Grid.Differential.Square.Decomposition

/-!
# Rectangle--initial-side pentagon decompositions

The initial-side part of the commutation map contributes two-step domains in both orders:
a rectangle in the original diagram followed by a pentagon, or a pentagon followed by a
rectangle in the commuted diagram. Each is an ordinary rectangle decomposition with a
distinguished initial side and turn row. The pentagon is recovered from those constraints;
no additional domain data is carried.

The finite families below select empty, `X`-avoiding domains. Their weights use variables
of the commuted diagram: rename the original rectangle weight in the first order, and use
the commuted rectangle weight in the second. Disjoint-side reordering identifies the two
contributions; common-side domains require separate recuts, sometimes involving terminal-side
pentagons.

The construction follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*,
Section 5.1, and the existing terminal-side decomposition API.
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

end GridDiagram

end TauCeti
