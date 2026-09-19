/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
public import TauCeti.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup.FinTwo

/-!
# Projective translations of the upper half-plane

The projective upper unipotent matrix acts by real translation. This identifies conjugated
parabolic stabilizers with the translations used in cusp coordinates.
-/

public section

open Matrix.ProjectiveSpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups

namespace TauCeti.UpperHalfPlane

/-- The projective upper unipotent matrix acts by real translation. -/
@[simp]
theorem upperRightHom_smul (x : ℝ) (z : ℍ) : upperRightHom x • z = x +ᵥ z := by
  rw [upperRightHom_apply, pslMk_smul]
  apply UpperHalfPlane.coe_injective
  rw [coe_specialLinearGroup_apply]
  simp [Matrix.SpecialLinearGroup.transvection_coe, coe_vadd, add_comm]

/-- A transformation conjugating an element to a translation sends its integer-power action
to translation by the corresponding integer multiple. -/
theorem smul_zpow_smul {σ γ : PSL(2, ℝ)} {w : ℝ}
    (h : σ * γ * σ⁻¹ = upperRightHom w) (n : ℤ) (z : ℍ) :
    σ • (γ ^ n • z) = ((n : ℝ) * w) +ᵥ (σ • z) := by
  have hsmul := congrArg (fun g : PSL(2, ℝ) ↦ g • (σ • z))
    (mul_zpow_mul_inv_eq_upperRightHom h n)
  simpa only [mul_smul, inv_smul_smul, upperRightHom_smul] using hsmul

end TauCeti.UpperHalfPlane
