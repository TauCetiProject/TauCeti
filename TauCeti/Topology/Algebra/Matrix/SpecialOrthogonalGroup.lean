/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
# Compactness of real special orthogonal matrix groups

The real special orthogonal group is compact in the subspace topology inherited from the matrix
space. Its defining orthogonality and determinant equations cut out a closed set, while each
matrix entry lies in `[-1, 1]` because every row has squared Euclidean norm one. Thus the group is
a closed subset of a compact matrix cube.

## Main results

* `Matrix.SpecialOrthogonalGroup.isCompact`: the real special orthogonal matrices form a compact
  set.
* `Matrix.SpecialOrthogonalGroup.instCompactSpace`: the corresponding matrix group is a compact
  space.
-/

public section

open Set

namespace Matrix.SpecialOrthogonalGroup

universe u

variable (n : Type u) [Fintype n] [DecidableEq n]

attribute [local instance] starRingOfComm

/-- The real special orthogonal matrices form a compact subset of the matrix space. -/
theorem isCompact :
    IsCompact (Matrix.specialOrthogonalGroup n ℝ : Set (Matrix n n ℝ)) := by
  have hclosed : IsClosed {A : Matrix n n ℝ | A * Aᵀ = 1 ∧ A.det = 1} :=
    (isClosed_eq (continuous_id.mul continuous_id.matrix_transpose) continuous_const).and
      (isClosed_eq continuous_id.matrix_det continuous_const)
  have hsubset : {A : Matrix n n ℝ | A * Aᵀ = 1 ∧ A.det = 1} ⊆
      (Set.Icc (-1 : ℝ) 1).matrix := by
    intro A hA i j
    have hrow : ∑ k, A i k * A i k = 1 := by
      calc
        ∑ k, A i k * A i k = (A * Aᵀ) i i := by simp [Matrix.mul_apply]
        _ = (1 : Matrix n n ℝ) i i := congrArg (fun M : Matrix n n ℝ => M i i) hA.1
        _ = 1 := by simp
    have hterm : A i j * A i j ≤ ∑ k, A i k * A i k :=
      Finset.single_le_sum (fun k _ => mul_self_nonneg (A i k)) (Finset.mem_univ j)
    constructor <;> nlinarith [sq_nonneg (A i j)]
  convert IsCompact.of_isClosed_subset
    ((isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)).matrix) hclosed hsubset using 1
  ext A
  change A ∈ Matrix.specialOrthogonalGroup n ℝ ↔ A * Aᵀ = 1 ∧ A.det = 1
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]

/-- The real special orthogonal matrix group is a compact space. -/
instance instCompactSpace : CompactSpace (Matrix.specialOrthogonalGroup n ℝ) :=
  isCompact_iff_compactSpace.mp (isCompact n)

end Matrix.SpecialOrthogonalGroup
