/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Cone.Dual
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

* `TauCeti.closedChamber`: the closed chamber of `X` for a family of linear forms `α_i`, as the
  dual pointed cone `PointedCone.dual` of the forms `α_i(X) α_i`, so that the `PointedCone` API
  (convexity, closure under addition and nonnegative scalars, the cone order) applies to it.

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
opposite to its sign at `X`, defined as the dual cone of the forms `α_i(X) α_i` under the evaluation
pairing. For the roots of a root-plane decomposition and an `X` at which no root vanishes, this is
the closed Weyl chamber containing `X`. -/
def closedChamber (α : ι → Dual ℝ V) (X : V) : PointedCone ℝ V :=
  PointedCone.dual LinearMap.id (Set.range fun i ↦ α i X • α i)

/-- Membership in the closed chamber of `X` is the sign condition on every form. -/
@[simp]
theorem mem_closedChamber {α : ι → Dual ℝ V} {X p : V} :
    p ∈ closedChamber α X ↔ ∀ i, 0 ≤ α i p * α i X := by
  simp [closedChamber, mul_comm]

/-- Every point at which all the forms vanish lies in every closed chamber. -/
theorem mem_closedChamber_of_forall_eq_zero {α : ι → Dual ℝ V} {X p : V} (hp : ∀ i, α i p = 0) :
    p ∈ closedChamber α X :=
  mem_closedChamber.mpr fun i ↦ by simp [hp i]

/-- `X` lies in its own closed chamber. -/
theorem self_mem_closedChamber (α : ι → Dual ℝ V) (X : V) : X ∈ closedChamber α X :=
  mem_closedChamber.mpr fun i ↦ mul_self_nonneg (α i X)

/-- The closed chamber of `X` is closed in a finite-dimensional Hausdorff topological vector
space. -/
theorem isClosed_closedChamber [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    [T2Space V] [FiniteDimensional ℝ V] (α : ι → Dual ℝ V) (X : V) :
    IsClosed (closedChamber α X : Set V) :=
  PointedCone.isClosed_dual fun f ↦ f.continuous_of_finiteDimensional

end TauCeti
