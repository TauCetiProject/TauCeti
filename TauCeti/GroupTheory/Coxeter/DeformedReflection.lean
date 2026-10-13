/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.Graph
public import TauCeti.Combinatorics.SimpleGraph.AdditiveFunction
public import Mathlib.LinearAlgebra.Reflection
public import Mathlib.LinearAlgebra.Pi
public import TauCeti.LinearAlgebra.Matrix.OneSubVecMulVec
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Deformed simple reflections of a finite graph

For a unit `q` in a commutative ring, the graph Cartan rows have diagonal coefficient
`1 + q²` and edge coefficient `q`. Subtracting the value of a row times its vertex vector
gives a linear automorphism. Its inverse subtracts `q⁻²` times the same row.

These transformations satisfy the graph's Artin relations. At `q = -1` the Cartan rows
are the rows of `SimpleGraph.graphCartanMatrix`, and the transformations are the standard
simple reflections.
The construction uses the existing rank-one matrix calculus `TauCeti.oneSubVecMulVecGL`
and its commutation and braid theorems. The ordinary specialization uses `Module.reflection`.

The vertex module and its operators are defined algebraically; identifying them with
graded Grothendieck classes requires a separate comparison.

## References

* Huerfano--Khovanov, *A category for the adjoint representation*, Section 2.2, equation (11),
  for the Cartan coefficients, and Section 4.6 for the evaluation-complex braid action.
  The identity-minus-row sign here corresponds to placing the evaluation term in degree `-1`.
* Khovanov--Seidel, *Quivers, Floer cohomology, and braid group actions*, Section 2e.1 and
  Proposition 2.8, for the type-A reduced Burau formulas. Replace the grading parameter by `q²`;
  rescaling the vertex vector at `j` by `qʲ` gives the symmetric edge coefficient used here.
-/

public section
noncomputable section

namespace SimpleGraph

universe u v
variable {V : Type u} [DecidableEq V] {R : Type v} [CommRing R]
  (G : SimpleGraph V)

/-- The diagonal and edge coefficients of the deformed graph Cartan matrix. -/
def deformedCartanEntry (q : R) (i j : V) : R := by
  classical
  exact ((1 + q ^ 2) • (1 : Matrix V V R) + q • G.adjMatrix R) i j

/-- The diagonal coefficient of a deformed Cartan row. -/
@[simp]
theorem deformedCartanEntry_self (q : R) (i : V) :
    G.deformedCartanEntry q i i = 1 + q ^ 2 := by
  classical
  simp [deformedCartanEntry, SimpleGraph.adjMatrix_apply]

/-- The coefficient at an adjacent vertex. -/
@[simp]
theorem deformedCartanEntry_of_adj (q : R) {i j : V} (h : G.Adj i j) :
    G.deformedCartanEntry q i j = q := by
  classical
  simp [deformedCartanEntry, SimpleGraph.adjMatrix_apply, h.ne, h]

/-- The coefficient at a distinct nonadjacent vertex. -/
@[simp]
theorem deformedCartanEntry_of_not_adj (q : R) {i j : V}
    (hne : i ≠ j) (h : ¬ G.Adj i j) : G.deformedCartanEntry q i j = 0 := by
  classical
  simp [deformedCartanEntry, SimpleGraph.adjMatrix_apply, hne, h]

variable [Fintype V]

/-- A row of the deformed graph Cartan matrix as a linear functional on vertex coordinates. -/
def deformedCartanRow (q : R) (i : V) : Module.Dual R (V → R) :=
  (LinearMap.proj i).comp (Matrix.mulVecLin (G.deformedCartanEntry q))

/-- A Cartan row is the sum of its coefficients times the vertex coordinates. -/
theorem deformedCartanRow_apply (q : R) (i : V) (x : V → R) :
    G.deformedCartanRow q i x = ∑ j, G.deformedCartanEntry q i j * x j := by
  rw [deformedCartanRow.eq_def]
  -- Unfold the linear-map composition/projection and `mulVecLin`: `mulVec` is this dot-product sum.
  rfl

@[simp]
theorem deformedCartanRow_single (q : R) (i j : V) :
    G.deformedCartanRow q i (Pi.single j 1) = G.deformedCartanEntry q i j := by
  classical
  rw [deformedCartanRow_apply]
  simp [Pi.single_apply]

private def deformedReflectionGL (q : Rˣ) (i : V) : Matrix.GeneralLinearGroup V R :=
  TauCeti.oneSubVecMulVecGL (q ^ 2) (Pi.single i 1) (G.deformedCartanEntry (q : R) i)
    (by simp [deformedCartanEntry_self, add_comm])

local notation "matrixLinearEquiv" =>
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv R (V → R))

/-- The deformed simple reflection at a vertex, in functional composition order. -/
def deformedReflection (q : Rˣ) (i : V) : (V → R) ≃ₗ[R] (V → R) :=
  matrixLinearEquiv (G.deformedReflectionGL q i)

/-- A deformed reflection subtracts its Cartan-row value in the vertex direction. -/
theorem deformedReflection_apply (q : Rˣ) (i : V) (x : V → R) :
    G.deformedReflection q i x =
      x - G.deformedCartanRow (q : R) i x • Pi.single i 1 := by
  simp only [deformedReflection, MulEquiv.trans_apply, deformedReflectionGL,
    TauCeti.oneSubVecMulVecGL_toLinearEquiv_apply, deformedCartanRow_apply, dotProduct]

/-- The inverse subtracts `q⁻²` times the same Cartan-row value. -/
theorem deformedReflection_symm_apply (q : Rˣ) (i : V) (x : V → R) :
    (G.deformedReflection q i).symm x =
      x - ((↑q⁻¹ : R) ^ 2 * G.deformedCartanRow (q : R) i x) • Pi.single i 1 := by
  simp only [deformedReflection, MulEquiv.trans_apply, deformedReflectionGL,
    TauCeti.oneSubVecMulVecGL_toLinearEquiv_symm_apply, deformedCartanRow_apply, dotProduct]
  simp

/-- Distinct nonadjacent vertex operators commute. -/
theorem deformedReflection_commute (q : Rˣ) {i j : V}
    (hne : i ≠ j) (h : ¬ G.Adj i j) :
    G.deformedReflection q i * G.deformedReflection q j =
      G.deformedReflection q j * G.deformedReflection q i := by
  have hji : ¬ G.Adj j i := fun h' ↦ h h'.symm
  have hmatrix : G.deformedReflectionGL q i * G.deformedReflectionGL q j =
      G.deformedReflectionGL q j * G.deformedReflectionGL q i := by
    apply Units.ext
    simp only [Units.val_mul, deformedReflectionGL, TauCeti.coe_oneSubVecMulVecGL]
    apply TauCeti.one_sub_vecMulVec_mul_comm
    · simp only [dotProduct_single_one, G.deformedCartanEntry_of_not_adj (q : R) hne h]
    · simp only [dotProduct_single_one,
        G.deformedCartanEntry_of_not_adj (q : R) (Ne.symm hne) hji]
  simpa only [map_mul, deformedReflection] using congrArg matrixLinearEquiv hmatrix

/-- Adjacent vertex operators satisfy the length-three braid relation. -/
theorem deformedReflection_braid (q : Rˣ) {i j : V} (h : G.Adj i j) :
    G.deformedReflection q i * G.deformedReflection q j * G.deformedReflection q i =
      G.deformedReflection q j * G.deformedReflection q i * G.deformedReflection q j := by
  have hmatrix : G.deformedReflectionGL q i * G.deformedReflectionGL q j *
      G.deformedReflectionGL q i = G.deformedReflectionGL q j *
        G.deformedReflectionGL q i * G.deformedReflectionGL q j := by
    apply Units.ext
    simp only [Units.val_mul, deformedReflectionGL, TauCeti.coe_oneSubVecMulVecGL]
    apply TauCeti.one_sub_vecMulVec_braid
    · simp only [dotProduct_single_one, deformedCartanEntry_self,
        G.deformedCartanEntry_of_adj (q : R) h, G.deformedCartanEntry_of_adj (q : R) h.symm,
        pow_two]
    · simp only [dotProduct_single_one, deformedCartanEntry_self,
        G.deformedCartanEntry_of_adj (q : R) h, G.deformedCartanEntry_of_adj (q : R) h.symm,
        pow_two]
  simpa only [map_mul, deformedReflection] using congrArg matrixLinearEquiv hmatrix

/-- The deformed reflections define a linear representation of the graph's Artin group. -/
def deformedReflectionRepresentation (q : Rˣ) :
    TauCeti.ArtinGroup G.coxeterMatrix →* ((V → R) ≃ₗ[R] (V → R)) :=
  G.artinGroupLift (G.deformedReflection q)
    (G.deformedReflection_commute q) (G.deformedReflection_braid q)

/-- The representation sends each Artin generator to its vertex operator. -/
@[simp]
theorem deformedReflectionRepresentation_gen (q : Rˣ) (i : V) :
    G.deformedReflectionRepresentation q (TauCeti.ArtinGroup.gen G.coxeterMatrix i) =
      G.deformedReflection q i := by
  simp only [deformedReflectionRepresentation, artinGroupLift_gen]

/-- An inverse Artin generator acts by the inverse vertex operator. -/
@[simp]
theorem deformedReflectionRepresentation_gen_inv (q : Rˣ) (i : V) :
    G.deformedReflectionRepresentation q (TauCeti.ArtinGroup.gen G.coxeterMatrix i)⁻¹ =
      (G.deformedReflection q i).symm := by
  rw [map_inv, deformedReflectionRepresentation_gen]
  exact LinearEquiv.ext fun x ↦ by simp only [LinearEquiv.coe_inv]

/-- The vertex direction is multiplied by `-q²`. -/
@[simp]
theorem deformedReflection_single_self (q : Rˣ) (i : V) :
    G.deformedReflection q i (Pi.single i 1) = -(q : R) ^ 2 • Pi.single i 1 := by
  rw [deformedReflection_apply, deformedCartanRow_single, deformedCartanEntry_self]
  module

/-- An adjacent vertex direction acquires `-q` times the reflecting direction. -/
@[simp]
theorem deformedReflection_single_of_adj (q : Rˣ) {i j : V} (h : G.Adj i j) :
    G.deformedReflection q i (Pi.single j 1) =
      Pi.single j 1 - (q : R) • Pi.single i 1 := by
  rw [deformedReflection_apply, deformedCartanRow_single,
    G.deformedCartanEntry_of_adj (q : R) h]

/-- A distinct nonadjacent vertex direction is fixed. -/
@[simp]
theorem deformedReflection_single_of_not_adj (q : Rˣ) {i j : V}
    (hne : i ≠ j) (h : ¬ G.Adj i j) :
    G.deformedReflection q i (Pi.single j 1) = Pi.single j 1 := by
  rw [deformedReflection_apply, deformedCartanRow_single,
    G.deformedCartanEntry_of_not_adj (q : R) hne h]
  simp

/-- At `q = -1`, a deformed reflection is Mathlib's ordinary simple reflection. -/
theorem deformedReflection_neg_one (i : V) :
    G.deformedReflection (-1 : Rˣ) i =
      Module.reflection (x := Pi.single i 1) (f := G.deformedCartanRow (-1 : R) i)
        (by rw [deformedCartanRow_single, deformedCartanEntry_self]; ring) := by
  apply LinearEquiv.ext
  intro x
  rw [deformedReflection_apply, Module.reflection_apply]
  simp

variable [DecidableRel G.Adj]

/-- The specialized Cartan row has the entries of the canonical graph Cartan matrix. -/
theorem deformedCartanRow_neg_one_single (i j : V) :
    G.deformedCartanRow (-1 : R) i (Pi.single j 1) =
      G.graphCartanMatrix R i j := by
  rw [deformedCartanRow_single, graphCartanMatrix_apply]
  rcases eq_or_ne i j with rfl | hij
  · simp only [deformedCartanEntry_self, neg_one_sq, one_add_one_eq_two, ite_true]
  · by_cases h : G.Adj i j
    · simp only [G.deformedCartanEntry_of_adj (-1 : R) h, hij, h, ite_false, ite_true]
    · simp only [G.deformedCartanEntry_of_not_adj (-1 : R) hij h, hij, h, ite_false]

end SimpleGraph
