/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Metrizable.Basic

/-!
# Topological properties of matrices

Mathlib gives `Matrix m n α` the product topology of `m → n → α`, so for finite index types it is
pseudo-metrizable whenever `α` is. This makes metrizable-codomain results, such as measurability
of pointwise limits of measurable maps, available for matrix-valued functions without choosing a
matrix norm.

Over a topological field, the inverse of a matrix-valued function that is continuous at a point
with invertible value is continuous there (`ContinuousAt.matrix_inv`), and so are its entries
(`ContinuousAt.matrix_inv_apply`).

The Kronecker product of two continuously varying matrices is continuous in the product topology.
-/

public section

namespace TauCeti

/-- A space of matrices with finitely many rows and columns over a pseudo-metrizable space is
pseudo-metrizable. -/
instance {m n α : Type*} [Finite m] [Finite n] [TopologicalSpace α]
    [TopologicalSpace.PseudoMetrizableSpace α] :
    TopologicalSpace.PseudoMetrizableSpace (Matrix m n α) :=
  -- The topology of `Matrix m n α` is by definition the product topology on `m → n → α`.
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (m → n → α))

end TauCeti

section Inverse

variable {X n K : Type*} [TopologicalSpace X] [Fintype n] [DecidableEq n] [Field K]
  [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K] {A : X → Matrix n n K} {x : X}

/-- The inverse of a matrix-valued function is continuous at every point where the function is
continuous and its value is invertible. -/
theorem ContinuousAt.matrix_inv (hA : ContinuousAt A x) (hdet : (A x).det ≠ 0) :
    ContinuousAt (fun y ↦ (A y)⁻¹) x :=
  (continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hdet)).comp hA

/-- The entries of the inverse of a matrix-valued function are continuous at every point where the
function is continuous and its value is invertible. -/
theorem ContinuousAt.matrix_inv_apply (hA : ContinuousAt A x) (hdet : (A x).det ≠ 0) (k l : n) :
    ContinuousAt (fun y ↦ (A y)⁻¹ k l) x :=
  (continuous_apply_apply k l).continuousAt.comp (hA.matrix_inv hdet)

end Inverse

open scoped Kronecker

/-- The Kronecker product of two continuous matrix-valued functions is continuous. -/
@[continuity, fun_prop]
theorem Continuous.matrix_kronecker {X R l m n p : Type*} [TopologicalSpace X]
    [TopologicalSpace R] [Mul R] [ContinuousMul R]
    {A : X → Matrix l m R} {B : X → Matrix n p R}
    (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun x ↦ A x ⊗ₖ B x) := by
  apply continuous_matrix
  intro i j
  simp only [Matrix.kroneckerMap_apply]
  exact (hA.matrix_elem i.1 j.1).mul (hB.matrix_elem i.2 j.2)
