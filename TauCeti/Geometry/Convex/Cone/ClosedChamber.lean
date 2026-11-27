/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The closed chamber of a family of linear forms

For linear forms `α_i` on a real vector space `V` and `X ∈ V`, the closed chamber of `X` is

`{p ∈ V | α_i(p) α_i(X) ≥ 0 for every i}`,

the set of points at which no `α_i` has the sign opposite to its sign at `X`. It is a convex cone
containing `X` and every point at which all `α_i` vanish, and it is closed in a finite-dimensional
Hausdorff topological vector space. For the roots of a root-plane decomposition of a compact Lie
algebra and an `X` at which no root vanishes, it is the closed Weyl chamber containing `X`.

## Main definitions

* `TauCeti.closedChamber`: the closed chamber of `X` for a family of linear forms `α_i`.

## Main results

* `TauCeti.isClosed_closedChamber`: the closed chamber is closed in finite dimension.
* `TauCeti.convex_closedChamber`, `TauCeti.smul_mem_closedChamber`,
  `TauCeti.add_mem_closedChamber`: the closed chamber is a convex cone.
* `TauCeti.mem_closedChamber_of_forall_eq_zero`, `TauCeti.zero_mem_closedChamber`,
  `TauCeti.self_mem_closedChamber`: basic memberships.
-/

public section

open Module

namespace TauCeti

variable {ι V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **The closed chamber of `X`.** For linear forms `α_i` on a real vector space `V` and `X ∈ V`,
the closed convex cone `{p | α_i(p) α_i(X) ≥ 0 for every i}` of the points at which no `α_i` has
the sign opposite to its sign at `X`. For the roots of a root-plane decomposition and an `X` at
which no root vanishes, this is the closed Weyl chamber containing `X`. -/
def closedChamber (α : ι → Dual ℝ V) (X : V) : Set V :=
  {p | ∀ i, 0 ≤ α i p * α i X}

/-- Membership in the closed chamber of `X` is the sign condition on every form. -/
@[simp]
theorem mem_closedChamber {α : ι → Dual ℝ V} {X p : V} :
    p ∈ closedChamber α X ↔ ∀ i, 0 ≤ α i p * α i X :=
  Iff.rfl

/-- Every point at which all the forms vanish lies in every closed chamber. -/
theorem mem_closedChamber_of_forall_eq_zero {α : ι → Dual ℝ V} {X p : V} (hp : ∀ i, α i p = 0) :
    p ∈ closedChamber α X :=
  fun i ↦ by simp [hp i]

/-- The origin lies in every closed chamber. -/
theorem zero_mem_closedChamber (α : ι → Dual ℝ V) (X : V) : 0 ∈ closedChamber α X :=
  mem_closedChamber_of_forall_eq_zero fun i ↦ map_zero (α i)

/-- `X` lies in its own closed chamber. -/
theorem self_mem_closedChamber (α : ι → Dual ℝ V) (X : V) : X ∈ closedChamber α X :=
  fun i ↦ mul_self_nonneg (α i X)

/-- The closed chamber is closed under multiplication by nonnegative scalars. -/
theorem smul_mem_closedChamber {α : ι → Dual ℝ V} {X p : V} (hp : p ∈ closedChamber α X)
    {c : ℝ} (hc : 0 ≤ c) : c • p ∈ closedChamber α X := fun i ↦ by
  rw [map_smul, smul_eq_mul, mul_assoc]
  exact mul_nonneg hc (hp i)

/-- The closed chamber is closed under addition. -/
theorem add_mem_closedChamber {α : ι → Dual ℝ V} {X p q : V} (hp : p ∈ closedChamber α X)
    (hq : q ∈ closedChamber α X) : p + q ∈ closedChamber α X := fun i ↦ by
  rw [map_add, add_mul]
  exact add_nonneg (hp i) (hq i)

/-- The closed chamber is convex. -/
theorem convex_closedChamber (α : ι → Dual ℝ V) (X : V) : Convex ℝ (closedChamber α X) :=
  fun _ hp _ hq _ _ ha hb _ ↦
    add_mem_closedChamber (smul_mem_closedChamber hp ha) (smul_mem_closedChamber hq hb)

/-- The closed chamber of `X` is closed in a finite-dimensional Hausdorff topological vector
space. -/
theorem isClosed_closedChamber [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    [T2Space V] [FiniteDimensional ℝ V] (α : ι → Dual ℝ V) (X : V) :
    IsClosed (closedChamber α X) := by
  simp only [closedChamber, Set.ofPred_forall]
  exact isClosed_iInter fun i ↦ isClosed_le continuous_const
    ((α i).continuous_of_finiteDimensional.mul continuous_const)

end TauCeti
