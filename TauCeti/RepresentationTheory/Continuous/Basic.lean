/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.RepresentationTheory.Continuous.Basic
import Mathlib.Dynamics.FixedPoints.Topology

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
* `ContRepresentation.isClosed_invariants`: the invariants of a representation on a Hausdorff
  space are closed, hence complete in a complete ambient space.
* `ContRepresentation.mem_invariants_restrict`: membership in the invariants of `π|_S` in terms
  of elements of `S`.
* `ContRepresentation.invariants_restrict_bot`, `ContRepresentation.invariants_restrict_top`:
  the invariants of the trivial and whole-group restrictions.
* `ContRepresentation.apply_mem_invariants_restrict`: for a normal subgroup `S`, the invariants
  of `π|_S` are `G`-stable.

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

section Closed

variable {R G V : Type*} [Ring R] [Monoid G] [AddCommGroup V] [Module R V]

/-- The invariants of a continuous representation on a Hausdorff space form a closed subspace: they
are the intersection of the closed fixed-point sets of the operators `π g`. -/
theorem isClosed_invariants [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
    (π : ContRepresentation R G V) :
    IsClosed (π.invariants : Set V) := by
  have h : (π.invariants : Set V) = ⋂ g, Function.fixedPoints (π g) := by
    ext
    simp [Function.IsFixedPt]
  rw [h]
  exact isClosed_iInter fun g ↦ isClosed_fixedPoints (π g).continuous

/-- The invariants of a continuous representation on a complete Hausdorff space are complete. -/
instance [UniformSpace V] [IsTopologicalAddGroup V] [CompleteSpace V] [T2Space V]
    (π : ContRepresentation R G V) :
    CompleteSpace π.invariants :=
  π.isClosed_invariants.completeSpace_coe

end Closed

section RestrictionInvariants

variable {R G V : Type*} [Ring R] [Group G] [AddCommGroup V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [Module R V]

-- Not `@[simp]`: `simp` already normalizes the left-hand side to the right-hand side through
-- `mem_invariants`, `restrict_apply_apply` and `Subtype.forall`, so the attribute would make this
-- a `simpNF` violation. This is the `rw`-usable form of that normalization.
/-- Membership in the invariants of `π|_S`, in terms of elements of `G` lying in `S`. -/
theorem mem_invariants_restrict {π : ContRepresentation R G V} {S : Subgroup G} {v : V} :
    v ∈ (π.restrict S.subtype).invariants ↔ ∀ s ∈ S, π s v = v :=
  ⟨fun hv s hs ↦ hv ⟨s, hs⟩, fun hv s ↦ hv (s : G) s.property⟩

/-- The trivial subgroup fixes everything. -/
@[simp]
theorem invariants_restrict_bot (π : ContRepresentation R G V) :
    (π.restrict (⊥ : Subgroup G).subtype).invariants = ⊤ := by
  ext v
  simp

/-- The invariants of the whole group are the invariants of `π`. -/
@[simp]
theorem invariants_restrict_top (π : ContRepresentation R G V) :
    (π.restrict (⊤ : Subgroup G).subtype).invariants = π.invariants :=
  SetLike.ext fun _ ↦ by simp [mem_invariants]

/-- For a normal subgroup `S`, the invariants of `π|_S` are a `G`-stable submodule. -/
theorem apply_mem_invariants_restrict (π : ContRepresentation R G V) (S : Subgroup G) [S.Normal]
    (g : G) (v : V) (hv : v ∈ (π.restrict S.subtype).invariants) :
    π g v ∈ (π.restrict S.subtype).invariants := by
  rw [mem_invariants_restrict] at hv ⊢
  intro s hs
  have hv' : π (g⁻¹ * s * g) v = v := hv _ ((‹S.Normal›).conj_mem' s hs g)
  have hg : s * g = g * (g⁻¹ * s * g) := by simp [mul_assoc]
  rw [← mul_apply_eq_comp, ← map_mul, hg, map_mul, mul_apply_eq_comp, hv']

end RestrictionInvariants

end ContRepresentation
