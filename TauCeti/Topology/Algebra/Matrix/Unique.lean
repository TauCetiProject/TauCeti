/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Unique
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Instances.Matrix

/-!
# `1 × 1` matrices as a topological monoid

For a singleton index type `m`, reading off the unique entry identifies the `1 × 1` matrices over
a (not necessarily unital or associative) semiring `A` with a topology with `A`, multiplicatively
and topologically (`Matrix.uniqueContinuousMulEquiv`), since the topology of `Matrix m m A` is the
product topology.

## Main definitions

* `Matrix.uniqueContinuousMulEquiv`: `Matrix m m A ≃ₜ* A` for `[Unique m]`.
-/

public section

namespace Matrix

variable (m A : Type*) [Fintype m] [Unique m] [NonUnitalNonAssocSemiring A] [TopologicalSpace A]

/-- Reading off the unique entry identifies `1 × 1` matrices over `A` with `A`, multiplicatively
and topologically. -/
def uniqueContinuousMulEquiv : Matrix m m A ≃ₜ* A where
  __ := uniqueEquiv
  map_mul' M N := by simp [Matrix.mul_apply]
  continuous_toFun := (continuous_apply default).comp (continuous_apply default)
  continuous_invFun := continuous_pi fun _ ↦ continuous_pi fun _ ↦ continuous_id

variable {m A} in
@[simp]
theorem uniqueContinuousMulEquiv_apply (M : Matrix m m A) :
    uniqueContinuousMulEquiv m A M = M default default :=
  (rfl)

variable {m A} in
@[simp]
theorem uniqueContinuousMulEquiv_symm_apply (a : A) :
    (uniqueContinuousMulEquiv m A).symm a = of fun _ _ ↦ a :=
  (rfl)

end Matrix
