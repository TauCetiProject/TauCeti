/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# The group of continuous linear automorphisms

Mathlib's `ContinuousLinearEquiv.automorphismGroup` makes `M ≃L[R] M` a group, with multiplication
`e * e' = e'.trans e`, identity `ContinuousLinearEquiv.refl` and inverse
`ContinuousLinearEquiv.symm`. This file records these identities and how the group operations act
on points, as Mathlib does for the group `M ≃ₗ[R] M` of linear automorphisms
(`LinearEquiv.one_eq_refl`, `LinearEquiv.mul_eq_trans`, `LinearEquiv.coe_inv`) and for the
permutation group (`Equiv.Perm.inv_def`). They are what is needed to compute with a
representation `G →* (M ≃L[R] M)` of a group by continuous linear automorphisms; for instance, the
inverses of such a representation are continuous whenever it is
(`MonoidHom.continuous_symm`).
-/

public section

namespace ContinuousLinearEquiv

variable {R M : Type*} [Semiring R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]

theorem one_eq_refl : (1 : M ≃L[R] M) = ContinuousLinearEquiv.refl R M := (rfl)

theorem mul_eq_trans (e e' : M ≃L[R] M) : e * e' = e'.trans e := (rfl)

theorem inv_def (e : M ≃L[R] M) : e⁻¹ = e.symm := (rfl)

@[simp]
theorem coe_inv (e : M ≃L[R] M) : ⇑e⁻¹ = ⇑e.symm := (rfl)

instance : IsOneApplyEqSelf (M ≃L[R] M) where

instance : IsMulApplyEqComp (M ≃L[R] M) where

end ContinuousLinearEquiv

namespace MonoidHom

/-- If a representation `π` of a topological group by continuous linear automorphisms depends
continuously on the group element, for the topology of bounded convergence on `M →L[𝕜] M` (the
operator norm topology when `M` is normed), then so do the inverses `(π g)⁻¹ = π g⁻¹`. -/
theorem continuous_symm {G 𝕜 M : Type*} [Group G] [TopologicalSpace G] [ContinuousInv G]
    [NormedField 𝕜] [AddCommGroup M] [Module 𝕜 M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    {π : G →* (M ≃L[𝕜] M)} (hπ : Continuous fun g ↦ (π g : M →L[𝕜] M)) :
    Continuous fun g ↦ ((π g).symm : M →L[𝕜] M) := by
  simp_rw [← ContinuousLinearEquiv.inv_def, ← map_inv]
  exact hπ.comp continuous_inv

end MonoidHom
