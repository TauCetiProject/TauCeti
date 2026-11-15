/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Derivation
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Basic

/-!
# The 2-dimensional Ginzburg generator data

For a finite quiver `Q`, this file adjoins a loop `tᵢ` at each vertex of its symmetrification,
constructs the signed local preprojective relator `ρᵢ` in the resulting path algebra, and defines
the proposed differential on arrows by `d(tᵢ) = ρᵢ` and zero on doubled arrows. It verifies the
cohomological and Adams degrees of this generator assignment. Extending it to the path algebra
and proving the differential graded identities remain future steps. No length-adic completion is
taken here.

This construction is the 2-dimensional Ginzburg model used by Etgü--Lekili, *Koszul duality
patterns in Floer theory*, Section 4, and Keller, *Deformed Calabi--Yau completions*, Section 6.5.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

variable (k : Type w) [CommRing k] {Q : Type u}

/-- The arrows from `i` to `j` in the symmetrified quiver of `Q`. -/
abbrev Ginzburg2DoubledHom {Q : Type u} [Quiver.{v} Q] (i j : Q) :=
  @Quiver.Hom.{v, u} (Symmetrify Q) (Quiver.symmetrifyQuiver Q) i j

/-- The vertices of the uncompleted 2-dimensional Ginzburg quiver are those of `Q`. -/
inductive Ginzburg2Quiver (Q : Type u)
  | vertex : Q → Ginzburg2Quiver Q
  deriving DecidableEq

namespace Ginzburg2Quiver

/-- The canonical equivalence from the original quiver to the Ginzburg vertex type. -/
def vertexEquiv : Q ≃ Ginzburg2Quiver Q where
  toFun := vertex
  invFun := fun x => by cases x with | vertex i => exact i
  left_inv _ := rfl
  right_inv x := by cases x with | vertex _ => rfl

@[simp] theorem vertexEquiv_symm_vertex (i : Q) : vertexEquiv.symm (vertex i) = i := by
  simp [vertexEquiv]

end Ginzburg2Quiver

variable [Quiver.{v} Q]

/-- The loop component records equality of the endpoints, so it contributes exactly one loop at
each vertex and none between distinct vertices. -/
abbrev Ginzburg2Arrow (Q : Type u) [Quiver.{v} Q]
    (i j : Ginzburg2Quiver Q) :=
  Ginzburg2DoubledHom (Ginzburg2Quiver.vertexEquiv.symm i)
    (Ginzburg2Quiver.vertexEquiv.symm j) ⊕ PLift (i = j)

instance : Quiver (Ginzburg2Quiver Q) where
  Hom i j := Ginzburg2Arrow Q i j

/-- Regard a doubled-quiver arrow as an arrow of the 2-dimensional Ginzburg quiver. -/
def Ginzburg2Arrow.doubledMap {i j : Q} (a : Ginzburg2DoubledHom i j) :
    Ginzburg2Quiver.vertex i ⟶ Ginzburg2Quiver.vertex j := Sum.inl a

/-- The loop at a vertex of the 2-dimensional Ginzburg quiver. -/
def Ginzburg2Arrow.loopMap (i : Q) :
    Ginzburg2Quiver.vertex i ⟶ Ginzburg2Quiver.vertex i := Sum.inr ⟨rfl⟩

/-- The cohomological degree of each arrow: doubled arrows have degree zero and added loops have
degree minus one. -/
def ginzburg2CohomologicalWeight :
    ∀ {i j : Ginzburg2Quiver Q}, (i ⟶ j) → ℤ
  | _, _, .inl _ => 0
  | _, _, .inr _ => -1

@[simp]
theorem ginzburg2CohomologicalWeight_doubledMap {i j : Q}
    (a : Ginzburg2DoubledHom i j) :
    ginzburg2CohomologicalWeight (Ginzburg2Arrow.doubledMap a) = 0 := by
  simp [ginzburg2CohomologicalWeight, Ginzburg2Arrow.doubledMap]

@[simp]
theorem ginzburg2CohomologicalWeight_loopMap (i : Q) :
    ginzburg2CohomologicalWeight (Ginzburg2Arrow.loopMap i) = -1 := by
  simp [ginzburg2CohomologicalWeight, Ginzburg2Arrow.loopMap]

/-- The Adams degree of each arrow: doubled arrows have degree one and added loops have degree
two. -/
def ginzburg2AdamsWeight : ∀ {i j : Ginzburg2Quiver Q}, (i ⟶ j) → ℤ
  | _, _, .inl _ => 1
  | _, _, .inr _ => 2

@[simp]
theorem ginzburg2AdamsWeight_doubledMap {i j : Q} (a : Ginzburg2DoubledHom i j) :
    ginzburg2AdamsWeight (Ginzburg2Arrow.doubledMap a) = 1 := by
  simp [ginzburg2AdamsWeight, Ginzburg2Arrow.doubledMap]

@[simp]
theorem ginzburg2AdamsWeight_loopMap (i : Q) :
    ginzburg2AdamsWeight (Ginzburg2Arrow.loopMap i) = 2 := by
  simp [ginzburg2AdamsWeight, Ginzburg2Arrow.loopMap]

variable [Fintype Q] [∀ i j : Q, Fintype (i ⟶ j)]

instance : Fintype (Ginzburg2Quiver Q) := Fintype.ofEquiv Q Ginzburg2Quiver.vertexEquiv

instance (i j : Q) : Fintype (Ginzburg2DoubledHom i j) := by
  letI := Quiver.symmetrifyQuiver Q
  -- Expose the symmetrified hom as the sum of arrows in both directions.
  change Fintype ((i ⟶ j) ⊕ (j ⟶ i))
  infer_instance

instance [DecidableEq Q] (i j : Ginzburg2Quiver Q) : Fintype (Ginzburg2Arrow Q i j) := by
  letI := Quiver.symmetrifyQuiver Q
  infer_instance

local notation "𝒢" => pathAlgebra k (Ginzburg2Quiver Q)

/-- The local preprojective relator included into the doubled-arrow part of the Ginzburg path
algebra. -/
noncomputable def ginzburg2Relator (i : Q) : 𝒢 :=
  (∑ j : Q, ∑ a : (j ⟶ i),
      ofArrow (Ginzburg2Arrow.doubledMap (Sum.inl a)) *
        ofArrow (Ginzburg2Arrow.doubledMap (Quiver.reverse (Sum.inl a)))) -
    ∑ j : Q, ∑ a : (i ⟶ j),
      ofArrow (Ginzburg2Arrow.doubledMap (Quiver.reverse (Sum.inl a))) *
        ofArrow (Ginzburg2Arrow.doubledMap (Sum.inl a))

/-- Homogeneous doubled arrows of degree `d` place the local relator in degree `d + d`. -/
private theorem ginzburg2Relator_mem_gradeBy
    (wt : ∀ {i j : Ginzburg2Quiver Q}, (i ⟶ j) → ℤ) (d : ℤ)
    (hwt : ∀ {i j : Q} (a : Ginzburg2DoubledHom i j), wt (Ginzburg2Arrow.doubledMap a) = d)
    (i : Q) :
    ginzburg2Relator k i ∈ gradeBy k wt (d + d) := by
  classical
  have hedge {u v : Q} (a : Ginzburg2DoubledHom u v) :
      (ofArrow (Ginzburg2Arrow.doubledMap a) : 𝒢) ∈ gradeBy k wt d := by
    rw [← hwt a]
    exact ofArrow_mem_gradeBy wt (Ginzburg2Arrow.doubledMap a)
  have hprod {u v : Q} (a : Ginzburg2DoubledHom u v) (b : Ginzburg2DoubledHom v u) :
      (ofArrow (Ginzburg2Arrow.doubledMap a) *
        ofArrow (Ginzburg2Arrow.doubledMap b) : 𝒢) ∈ gradeBy k wt (d + d) :=
    gradeBy_mul_gradeBy_le d d (Submodule.mul_mem_mul (hedge a) (hedge b))
  refine Submodule.sub_mem _
    (Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun a _ =>
      hprod (Sum.inl a) (Quiver.reverse (Sum.inl a)))
    (Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun a _ =>
      hprod (Quiver.reverse (Sum.inl a)) (Sum.inl a))

/-- The generator assignment for the differential: doubled arrows map to zero and each added
loop maps to its local preprojective relator. -/
noncomputable def ginzburg2DifferentialGenerator
    {i j : Ginzburg2Quiver Q} (a : i ⟶ j) : 𝒢 :=
  match a with
  | .inl _ => 0
  | .inr _ => ginzburg2Relator k (Ginzburg2Quiver.vertexEquiv.symm i)

@[simp]
theorem ginzburg2DifferentialGenerator_doubledMap {i j : Q}
    (a : Ginzburg2DoubledHom i j) :
    ginzburg2DifferentialGenerator k (Ginzburg2Arrow.doubledMap a) = 0 := by
  simp [ginzburg2DifferentialGenerator, Ginzburg2Arrow.doubledMap]

@[simp]
theorem ginzburg2DifferentialGenerator_loopMap (i : Q) :
    ginzburg2DifferentialGenerator k (Ginzburg2Arrow.loopMap i) = ginzburg2Relator k i := by
  simp [ginzburg2DifferentialGenerator, Ginzburg2Arrow.loopMap,
    Ginzburg2Quiver.vertexEquiv_symm_vertex]

/-- The generator assignment has cohomological degree one. -/
theorem ginzburg2DifferentialGenerator_cohomological_mem
    {i j : Ginzburg2Quiver Q} (a : i ⟶ j) :
    ginzburg2DifferentialGenerator k a ∈
      gradeBy k (ginzburg2CohomologicalWeight (Q := Q))
        (ginzburg2CohomologicalWeight a + 1) := by
  rcases i, j, a with ⟨⟨i⟩, ⟨j⟩, e | ⟨⟨⟩⟩⟩
  · simp [ginzburg2DifferentialGenerator]
  · simpa [ginzburg2DifferentialGenerator, ginzburg2CohomologicalWeight] using
      ginzburg2Relator_mem_gradeBy k ginzburg2CohomologicalWeight 0
        ginzburg2CohomologicalWeight_doubledMap i

/-- The generator assignment preserves the Adams degree. -/
theorem ginzburg2DifferentialGenerator_adams_mem
    {i j : Ginzburg2Quiver Q} (a : i ⟶ j) :
    ginzburg2DifferentialGenerator k a ∈
      gradeBy k (ginzburg2AdamsWeight (Q := Q)) (ginzburg2AdamsWeight a) := by
  rcases i, j, a with ⟨⟨i⟩, ⟨j⟩, e | ⟨⟨⟩⟩⟩
  · simp [ginzburg2DifferentialGenerator]
  · simpa [ginzburg2DifferentialGenerator, ginzburg2AdamsWeight] using
      ginzburg2Relator_mem_gradeBy k ginzburg2AdamsWeight 1
        ginzburg2AdamsWeight_doubledMap i

/-! The remaining construction extends this assignment by the graded derivation, proves its
square-zero and Leibniz identities, and then compares degree-zero cohomology with the
preprojective algebra. -/

end TauCeti
