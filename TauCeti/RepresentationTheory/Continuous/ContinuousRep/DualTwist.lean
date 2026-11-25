/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.ContinuousRep.Operations
public import Mathlib.Topology.Algebra.Group.Units

/-!
# The contragredient of a twist and of a character line

For a continuous representation `ρ` on a finite projective module and a continuous character `χ`,
the contragredient of the twist is the twist of the contragredient by the inverse character,
`M(χ)^∨ = M^∨(χ⁻¹)` (`TauCeti.ContinuousRep.dual_twist`), and the contragredient of the line of
`χ` is the line of `χ⁻¹` (`TauCeti.ContinuousRep.dualOfCharacterIso`), through evaluation at `1`,
`Hom_A(A, A) ≅ A`. A definition of the dual by the transpose without the inverse would return `χ`.

## Main definitions

* `TauCeti.ContinuousRep.dualOfCharacterIso`: `A(χ)^∨ ≅ A(χ⁻¹)`.

## Main results

* `TauCeti.ContinuousRep.dual_twist`: `M(χ)^∨ = M^∨(χ⁻¹)`.
-/

public section

noncomputable section

namespace TauCeti.ContinuousRep

variable {Γ A : Type*} [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ] [CommRing A]
  [TopologicalSpace A] [IsTopologicalRing A]

/-- **The contragredient of a twist** is the twist of the contragredient by the inverse character:
`M(χ)^∨ = M^∨(χ⁻¹)`. -/
theorem dual_twist {M : Type*} [AddCommGroup M] [Module A M] [TopologicalSpace M]
    [IsModuleTopology A M] [Module.Finite A M] [Module.Projective A M]
    [TopologicalSpace (Module.Dual A M)] [IsModuleTopology A (Module.Dual A M)]
    [ContinuousSMul A M] [ContinuousSMul A (Module.Dual A M)]
    (ρ : ContinuousRep Γ A M) (χ : Γ →ₜ* Aˣ) : (ρ.twist χ).dual = ρ.dual.twist χ⁻¹ :=
  ext fun g ψ => LinearMap.ext fun x => by
    simp only [dual_apply_apply, twist_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
      map_inv]
    rfl

variable [TopologicalSpace (Module.Dual A A)] [IsModuleTopology A (Module.Dual A A)]

/-- **The contragredient of a character line is the line of the inverse character**:
evaluation at `1` is an isomorphism `A(χ)^∨ ≅ A(χ⁻¹)`. -/
def dualOfCharacterIso (χ : Γ →ₜ* Aˣ) : Iso (ofCharacter χ).dual (ofCharacter χ⁻¹) :=
  Iso.ofEquiv (.mk (LinearMap.ringLmapEquivSelf A A A) fun g => LinearMap.ext fun ψ => by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.ringLmapEquivSelf_apply,
      coe_toRepresentation, dual_apply_apply, ofCharacter_apply, mul_one]
    rw [← mul_one (χ g⁻¹ : A), ← smul_eq_mul, map_smul, map_inv]
    rfl)

@[simp]
theorem dualOfCharacterIso_apply (χ : Γ →ₜ* Aˣ) (ψ : Module.Dual A A) :
    dualOfCharacterIso χ ψ = ψ 1 :=
  Iso.ofEquiv_apply _ _

end TauCeti.ContinuousRep
