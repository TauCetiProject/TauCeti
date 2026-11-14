/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Unitary
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Matrix.Unique

/-!
# Topological group equivalences for reindexed and `1 × 1` unitary matrices

Over any topological star semiring `α`:
* reindexing rows and columns along an equivalence `e : m ≃ n` induces an isomorphism of
  topological groups `Matrix.unitaryReindexContinuousMulEquiv` between `unitary (Matrix m m α)` and
  `unitary (Matrix n n α)`;
* for a singleton index type `m` (`[Unique m]`), reading off the unique entry via
  `Matrix.uniqueStarMulEquiv` induces an isomorphism of topological groups
  `Matrix.unitaryUniqueContinuousMulEquiv` between `unitary (Matrix m m α)` and `unitary α`.

## Main definitions

* `Matrix.unitaryReindexContinuousMulEquiv`: the isomorphism of topological groups
  `unitary (Matrix m m α) ≃ₜ* unitary (Matrix n n α)` induced by `e : m ≃ n`.
* `Matrix.unitaryUniqueContinuousMulEquiv`: the isomorphism of topological groups
  `unitary (Matrix m m α) ≃ₜ* unitary α` for `[Unique m]`.
-/

public section

namespace Matrix

section Reindex

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (α : Type*) [Semiring α] [StarRing α] [TopologicalSpace α]

/-- Reindexing rows and columns along an equivalence `e : m ≃ n` induces an isomorphism of
topological groups between `unitary (Matrix m m α)` and `unitary (Matrix n n α)`. -/
def unitaryReindexContinuousMulEquiv (e : m ≃ n) :
    unitary (Matrix m m α) ≃ₜ* unitary (Matrix n n α) where
  __ := (Unitary.mapEquiv
    { (reindexRingEquiv α e).toMulEquiv with map_star' := fun _ ↦ rfl }).toMulEquiv
  continuous_toFun := continuous_induced_rng.2 (continuous_subtype_val.matrix_reindex e e)
  continuous_invFun :=
    continuous_induced_rng.2 (continuous_subtype_val.matrix_reindex e.symm e.symm)

variable {α} in
@[simp]
theorem coe_unitaryReindexContinuousMulEquiv_apply (e : m ≃ n) (A : unitary (Matrix m m α)) :
    (unitaryReindexContinuousMulEquiv α e A : Matrix n n α) = reindex e e A.1 := by
  rfl

variable {α} in
@[simp]
theorem unitaryReindexContinuousMulEquiv_symm (e : m ≃ n) :
    (unitaryReindexContinuousMulEquiv α e).symm = unitaryReindexContinuousMulEquiv α e.symm := by
  rfl

end Reindex

section Unique

variable (m α : Type*) [Fintype m] [DecidableEq m] [Unique m]
  [Semiring α] [StarRing α] [TopologicalSpace α]

/-- Reading off the unique entry identifies `1 × 1` unitary matrices over `α` with `unitary α` as
topological groups. -/
def unitaryUniqueContinuousMulEquiv : unitary (Matrix m m α) ≃ₜ* unitary α where
  __ := (Unitary.mapEquiv (uniqueStarMulEquiv (m := m) (A := α))).toMulEquiv
  continuous_toFun :=
    continuous_induced_rng.2
      ((continuous_apply default).comp ((continuous_apply default).comp continuous_subtype_val))
  continuous_invFun :=
    continuous_induced_rng.2 (continuous_pi fun _ ↦ continuous_pi fun _ ↦ continuous_subtype_val)

variable {m α} in
@[simp]
theorem coe_unitaryUniqueContinuousMulEquiv_apply (A : unitary (Matrix m m α)) :
    (unitaryUniqueContinuousMulEquiv m α A : α) = A.1 default default := by
  rfl

variable {m α} in
@[simp]
theorem coe_unitaryUniqueContinuousMulEquiv_symm_apply (u : unitary α) :
    ((unitaryUniqueContinuousMulEquiv m α).symm u : Matrix m m α) =
      Matrix.of fun _ _ ↦ (u : α) := by
  rfl

end Unique

end Matrix
