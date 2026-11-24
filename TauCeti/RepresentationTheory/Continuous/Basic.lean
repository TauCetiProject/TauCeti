/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.RepresentationTheory.Continuous.Basic

/-!
# Basic facts about continuous representations

This file records elementary identities for Mathlib's `ContRepresentation` that hold for any
group, without topology on the group or measure theory. Forgetting continuity leaves the action
on each vector unchanged.

## Main results

* `ContRepresentation.toRepresentation_apply`: evaluation agrees with the continuous action.
* `ContRepresentation.comp_inv_self`: the action operator of `g` composed with that of `g⁻¹` is
  the identity.
* `ContRepresentation.map_mul_inv_comp`: `ρ (h * g)⁻¹ ∘ ρ h = ρ g⁻¹`.
* `ContRepresentation.comp_comp_inv_eq`: an intertwining relation `S ∘ ρ g = ρ' g ∘ T` gives
  `ρ' g ∘ T ∘ ρ g⁻¹ = S`.
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

/-- An action operator composed with the action of the inverse group element is the identity. -/
@[simp]
theorem comp_inv_self {R G V : Type*} [Ring R] [Group G] [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [Module R V] (ρ : ContRepresentation R G V) (g : G) :
    (ρ g).comp (ρ g⁻¹) = ContinuousLinearMap.id R V := by
  rw [← ContinuousLinearMap.mul_def, ← map_mul, mul_inv_cancel, map_one]
  rfl

/-- The action of `(h * g)⁻¹` undoes that of `h` up to the action of `g⁻¹`. -/
theorem map_mul_inv_apply {R G V : Type*} [Ring R] [Group G] [AddCommGroup V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [Module R V] (ρ : ContRepresentation R G V)
    (h g : G) (v : V) :
    ρ (h * g)⁻¹ (ρ h v) = ρ g⁻¹ v := by
  rw [mul_inv_rev, map_mul, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  congr 1
  simpa using ρ.apply_inv_apply (g := h⁻¹) (v := v)

/-- `ρ (h * g)⁻¹ ∘ ρ h = ρ g⁻¹`. -/
theorem map_mul_inv_comp {R G V : Type*} [Ring R] [Group G] [AddCommGroup V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [Module R V] (ρ : ContRepresentation R G V)
    (h g : G) :
    ρ (h * g)⁻¹ ∘L ρ h = ρ g⁻¹ :=
  ContinuousLinearMap.ext fun v ↦ ρ.map_mul_inv_apply h g v

/-- If `S ∘ ρ g = ρ' g ∘ T`, then `ρ' g ∘ T ∘ ρ g⁻¹ = S`. -/
theorem comp_comp_inv_eq {R G V V' : Type*} [Ring R] [Group G] [AddCommGroup V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [Module R V] [AddCommGroup V']
    [TopologicalSpace V'] [IsTopologicalAddGroup V'] [Module R V'] (ρ : ContRepresentation R G V)
    (ρ' : ContRepresentation R G V') (g : G) {S T : V →L[R] V'} (h : S ∘L ρ g = ρ' g ∘L T) :
    ρ' g ∘L T ∘L ρ g⁻¹ = S := by
  rw [← ContinuousLinearMap.comp_assoc, ← h, ContinuousLinearMap.comp_assoc, ρ.comp_inv_self,
    ContinuousLinearMap.comp_id]

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
