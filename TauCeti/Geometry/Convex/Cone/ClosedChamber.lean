/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The closed chamber of a family of linear forms

For linear forms `α_i` on a real vector space `V` and `X ∈ V`, the closed chamber of `X` is

`{p ∈ V | α_i(p) α_i(X) ≥ 0 for every i}`,

the set of points at which no `α_i` has the sign opposite to its sign at `X`. It is a pointed cone
containing `X` and every point at which all `α_i` vanish, and it is closed in a finite-dimensional
Hausdorff topological vector space. For the roots of a root-plane decomposition of a compact Lie
algebra and an `X` at which no root vanishes, it is the closed Weyl chamber containing `X`.

## Main definitions

* `TauCeti.closedChamber`: the closed chamber of `X` for a family of linear forms `α_i`, as a
  pointed cone, so that the `PointedCone` API (convexity, closure under addition and nonnegative
  scalars, the cone order) applies to it.

## Main results

* `TauCeti.isClosed_closedChamber`: the closed chamber is closed in finite dimension.
* `TauCeti.mem_closedChamber_of_forall_eq_zero`, `TauCeti.self_mem_closedChamber`: basic
  memberships.
-/

public section

open Module

namespace TauCeti

variable {ι V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **The closed chamber of `X`.** For linear forms `α_i` on a real vector space `V` and `X ∈ V`,
the pointed cone `{p | α_i(p) α_i(X) ≥ 0 for every i}` of the points at which no `α_i` has the sign
opposite to its sign at `X`. For the roots of a root-plane decomposition and an `X` at which no
root vanishes, this is the closed Weyl chamber containing `X`. -/
def closedChamber (α : ι → Dual ℝ V) (X : V) : PointedCone ℝ V where
  carrier := {p | ∀ i, 0 ≤ α i p * α i X}
  add_mem' hp hq i := by
    rw [map_add, add_mul]
    exact add_nonneg (hp i) (hq i)
  zero_mem' i := by simp
  smul_mem' c p hp i := by
    rw [← Nonneg.coe_smul, map_smul, smul_eq_mul, mul_assoc]
    exact mul_nonneg c.property (hp i)

/-- Membership in the closed chamber of `X` is the sign condition on every form. -/
@[simp]
theorem mem_closedChamber {α : ι → Dual ℝ V} {X p : V} :
    p ∈ closedChamber α X ↔ ∀ i, 0 ≤ α i p * α i X :=
  Iff.rfl

/-- Every point at which all the forms vanish lies in every closed chamber. -/
theorem mem_closedChamber_of_forall_eq_zero {α : ι → Dual ℝ V} {X p : V} (hp : ∀ i, α i p = 0) :
    p ∈ closedChamber α X :=
  fun i ↦ by simp [hp i]

/-- `X` lies in its own closed chamber. -/
theorem self_mem_closedChamber (α : ι → Dual ℝ V) (X : V) : X ∈ closedChamber α X :=
  fun i ↦ mul_self_nonneg (α i X)

/-- The closed chamber of `X` is closed in a finite-dimensional Hausdorff topological vector
space. -/
theorem isClosed_closedChamber [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    [T2Space V] [FiniteDimensional ℝ V] (α : ι → Dual ℝ V) (X : V) :
    IsClosed (closedChamber α X : Set V) := by
  simp only [← SetLike.setOfPred_mem_eq, mem_closedChamber, Set.ofPred_forall]
  exact isClosed_iInter fun i ↦ isClosed_le continuous_const
    ((α i).continuous_of_finiteDimensional.mul continuous_const)

end TauCeti
