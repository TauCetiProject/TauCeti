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

Mathlib's `ContinuousLinearEquiv.automorphismGroup` makes `M ≃L[R] M` a group whose unit is the
identity, whose product is composition and whose inverse is the inverse equivalence. This file
states these three laws (`ContinuousLinearEquiv.one_eq_refl`, `ContinuousLinearEquiv.mul_eq_trans`,
`ContinuousLinearEquiv.inv_eq_symm`), following Mathlib's `LinearEquiv.one_eq_refl` and
`LinearEquiv.mul_eq_trans`. As for `LinearEquiv`, the group operations act on points as the
identity and composition (`ContinuousLinearEquiv.coe_inv` and the `IsOneApplyEqSelf` and
`IsMulApplyEqComp` instances).

For a representation `π : G →* (M ≃L[𝕜] M)` of a topological group that is continuous in the
topology of bounded convergence, the inverse action `g ↦ (π g)⁻¹` is continuous as well
(`Continuous.continuous_symm_of_monoidHom`), since it is the action of `g⁻¹`.
-/

public section

namespace ContinuousLinearEquiv

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]

/-- The unit of the automorphism group is the identity equivalence. -/
theorem one_eq_refl : (1 : M ≃L[R] M) = .refl R M :=
  rfl

/-- The product in the automorphism group is composition. -/
theorem mul_eq_trans (f g : M ≃L[R] M) : f * g = g.trans f :=
  rfl

/-- The inverse in the automorphism group is the inverse equivalence. -/
theorem inv_eq_symm (f : M ≃L[R] M) : f⁻¹ = f.symm :=
  rfl

/-- The inverse in the automorphism group applies the inverse equivalence. -/
@[simp]
theorem coe_inv (f : M ≃L[R] M) : ⇑f⁻¹ = ⇑f.symm :=
  rfl

instance : IsOneApplyEqSelf (M ≃L[R] M) where

instance : IsMulApplyEqComp (M ≃L[R] M) where

end ContinuousLinearEquiv

/-- If a representation `π` of a topological group by continuous linear automorphisms is
continuous in the topology of bounded convergence, so is its inverse `g ↦ (π g)⁻¹`. -/
theorem Continuous.continuous_symm_of_monoidHom {G 𝕜 M : Type*} [Group G] [TopologicalSpace G]
    [ContinuousInv G] [NormedField 𝕜] [AddCommGroup M] [Module 𝕜 M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] {π : G →* (M ≃L[𝕜] M)} (hπ : Continuous fun g ↦ (π g : M →L[𝕜] M)) :
    Continuous fun g ↦ ((π g).symm : M →L[𝕜] M) :=
  (hπ.comp continuous_inv).congr fun g ↦ by
    rw [Function.comp_apply, map_inv, ContinuousLinearEquiv.inv_eq_symm]
