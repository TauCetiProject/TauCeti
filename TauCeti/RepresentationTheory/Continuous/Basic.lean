/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars

/-!
# Basic facts about continuous representations

This file records elementary identities for Mathlib's `ContRepresentation` that hold for any
group, without topology on the group or measure theory. Forgetting continuity leaves the action
on each vector unchanged.

## Main definitions

* `ContRepresentation.restrictScalars`: a continuous representation over `A`, read as a
  continuous representation over a compatibly acting ring `R`.

## Main results

* `ContRepresentation.toRepresentation_apply`: evaluation agrees with the continuous action.
* `ContRepresentation.restrictScalars_apply`: restricting scalars preserves evaluation on vectors.
* `ContRepresentation.comp_inv_self`: the action operator of `g` composed with that of `g⁻¹` is
  the identity.
* `ContRepresentation.apply_inr_apply_inl`: in a representation of a semidirect product
  `N ⋊[φ] K`, the operator of `k : K` intertwines the action of `n : N` with that of `φ k n`.

## References

* `Mathlib.RepresentationTheory.Continuous.Basic`, for `ContRepresentation.toRepresentation`.
-/

public section

namespace ContRepresentation

/-- Forgetting continuity of an action preserves its evaluation on vectors. -/
-- Normalize evaluation before the generic linear-map coercion rules expand its head.
@[simp↓]
theorem toRepresentation_apply {R G V : Type*} [Ring R] [Monoid G]
    [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [Module R V]
    (π : ContRepresentation R G V) (g : G) (v : V) :
    (π.toRepresentation : Representation R G V) g v = π g v := (rfl)

section RestrictScalars

variable {A G V : Type*} [Ring A] [Monoid G] [AddCommGroup V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [Module A V]

/-- A continuous representation on a topological `A`-module, read as a continuous representation
over a ring `R` acting compatibly with `A`: each operator is restricted to a continuous
`R`-linear map. Its operators are those of `π` (`ContRepresentation.restrictScalars_apply`). -/
def restrictScalars (R : Type*) [Ring R] [Module R V] [LinearMap.CompatibleSMul V V R A]
    (π : ContRepresentation A G V) : ContRepresentation R G V :=
  ofMonoidHom
    { toFun := fun g ↦ (π g).restrictScalars R
      map_one' := by ext; simp
      map_mul' := fun _ _ ↦ by ext; simp }

/-- Restricting the scalars of a continuous representation does not change its action on
vectors. -/
@[simp]
theorem restrictScalars_apply {R : Type*} [Ring R] [Module R V] [LinearMap.CompatibleSMul V V R A]
    (π : ContRepresentation A G V) (g : G) (v : V) :
    π.restrictScalars R g v = π g v :=
  (rfl)

end RestrictScalars

/-- An action operator composed with the action of the inverse group element is the identity. -/
@[simp]
theorem comp_inv_self {R G V : Type*} [Ring R] [Group G] [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [Module R V] (ρ : ContRepresentation R G V) (g : G) :
    (ρ g).comp (ρ g⁻¹) = ContinuousLinearMap.id R V := by
  rw [← ContinuousLinearMap.mul_def, ← map_mul, mul_inv_cancel, map_one]
  rfl

open SemidirectProduct in
/-- In a representation of a semidirect product `N ⋊[φ] K`, the operator of `k : K` intertwines
the action of `n : N` with the action of `φ k n`: `ρ k (ρ n v) = ρ (φ k n) (ρ k v)`. -/
theorem apply_inr_apply_inl {R N K V : Type*} [Ring R] [Group N] [Group K] [AddCommGroup V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [Module R V] {φ : K →* MulAut N}
    (ρ : ContRepresentation R (N ⋊[φ] K) V) (k : K) (n : N) (v : V) :
    ρ (inr k) (ρ (inl n) v) = ρ (inl (φ k n)) (ρ (inr k) v) := by
  rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul, inl_aut,
    map_inv, inv_mul_cancel_right]

end ContRepresentation
