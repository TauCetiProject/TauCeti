/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
import TauCeti.NumberTheory.ModularForms.JacobiTheta.Manifold
import TauCeti.NumberTheory.ModularForms.JacobiTheta.OneVariable
import TauCeti.NumberTheory.ModularForms.JacobiTheta.Product

/-!
# The theta automorphy factor on `SL(2, ℤ)`

Defines the weight-`1/2` theta automorphy factor
`TauCeti.thetaAutomorphyFactor γ z = jacobiTheta (2 * (γ • z)) / jacobiTheta (2 * z)` for
`γ ∈ SL(2, ℤ)` and `z ∈ ℍ`, and establishes its general `SL(2, ℤ)` properties: holomorphy on `ℍ`,
nonvanishing, the cocycle law `j(γ₁ * γ₂, z) = j(γ₁, γ₂ • z) * j(γ₂, z)`, invariance under `-γ`,
the inversion law, and triviality on integer translations `ModularGroup.T ^ n`.

## Main definitions

* `TauCeti.thetaAutomorphyFactor`: the theta automorphy factor
  `j(γ, z) = jacobiTheta (2 * (γ • z)) / jacobiTheta (2 * z)` for `γ ∈ SL(2, ℤ)` and `z ∈ ℍ`.

## Main results

* `TauCeti.mdifferentiable_thetaAutomorphyFactor`: `thetaAutomorphyFactor γ` is holomorphic on `ℍ`
  for every `γ ∈ SL(2, ℤ)`.
* `TauCeti.thetaAutomorphyFactor_mul`: the cocycle law
  `j(γ₁ * γ₂, z) = j(γ₁, γ₂ • z) * j(γ₂, z)` for all `γ₁, γ₂ ∈ SL(2, ℤ)`.
* `TauCeti.thetaAutomorphyFactor_neg`, `TauCeti.thetaAutomorphyFactor_inv`,
  `TauCeti.thetaAutomorphyFactor_T_zpow`: negation invariance, inversion, and translation
  invariance.
-/

public section

open Complex ModularGroup
open scoped Manifold MatrixGroups Real UpperHalfPlane

namespace TauCeti

/-- **The theta automorphy factor** `j(γ, z) = θ(2 · γ z) / θ(2 z)` for `γ ∈ SL(2, ℤ)` and
`z ∈ ℍ`. On `Γ₀(4)`, it equals Shimura's weight-`1/2` factor
`(thetaMultiplierPhase d)⁻¹ * kroneckerSym c d * Complex.sqrt (c z + d)`
(`TauCeti.thetaAutomorphyFactor_of_mem_Gamma0`). -/
noncomputable def thetaAutomorphyFactor (γ : SL(2, ℤ)) (z : ℍ) : ℂ :=
  jacobiTheta (2 * ((γ • z : ℍ) : ℂ)) / jacobiTheta (2 * (z : ℂ))

/-- Defining formula for `thetaAutomorphyFactor`. -/
theorem thetaAutomorphyFactor_def (γ : SL(2, ℤ)) (z : ℍ) :
    thetaAutomorphyFactor γ z = jacobiTheta (2 * ((γ • z : ℍ) : ℂ)) / jacobiTheta (2 * (z : ℂ)) :=
  (rfl)

/-- For each `γ ∈ SL(2, ℤ)`, `z ↦ thetaAutomorphyFactor γ z` is holomorphic on `ℍ`. -/
theorem mdifferentiable_thetaAutomorphyFactor (γ : SL(2, ℤ)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (thetaAutomorphyFactor γ) := fun z ↦ by
  have hsmul : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun w : ℍ ↦ γ • w) := fun w ↦ by
    have h := UpperHalfPlane.mdifferentiable_smul (g := Matrix.SpecialLinearGroup.mapGL ℝ γ)
      (by simp) w
    simpa only [Matrix.SpecialLinearGroup.mapGL_smul] using h
  have hθ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun w : ℍ ↦ jacobiTheta (2 * (w : ℂ))) := by
    simpa using mdifferentiable_jacobiTheta_natCast_mul 2
  have hne : ∀ w : ℍ, jacobiTheta (2 * (w : ℂ)) ≠ 0 := fun w ↦ by
    simpa using jacobiTheta_natCast_mul_ne_zero 2 w
  rw [funext (thetaAutomorphyFactor_def γ)]
  exact ((hθ.comp hsmul) z).div (hθ z) (hne z)

/-- The theta automorphy factor never vanishes on the upper half-plane. -/
@[simp]
theorem thetaAutomorphyFactor_ne_zero (γ : SL(2, ℤ)) (z : ℍ) :
    thetaAutomorphyFactor γ z ≠ 0 := by
  rw [thetaAutomorphyFactor_def]
  exact div_ne_zero (by simpa using jacobiTheta_natCast_mul_ne_zero 2 (γ • z))
    (by simpa using jacobiTheta_natCast_mul_ne_zero 2 z)

/-- Rewriting `θ(2 · γ z)` in terms of `thetaAutomorphyFactor γ z` and `θ(2 z)`. -/
theorem jacobiTheta_two_mul_smul_eq_thetaAutomorphyFactor_mul (γ : SL(2, ℤ)) (z : ℍ) :
    jacobiTheta (2 * ((γ • z : ℍ) : ℂ)) =
      thetaAutomorphyFactor γ z * jacobiTheta (2 * (z : ℂ)) := by
  rw [thetaAutomorphyFactor_def]
  exact (div_mul_cancel₀ _ (by simpa using jacobiTheta_natCast_mul_ne_zero 2 z)).symm

/-- **Cocycle law** for `thetaAutomorphyFactor` on all of `SL(2, ℤ)`:
`j(γ₁ * γ₂, z) = j(γ₁, γ₂ • z) * j(γ₂, z)`. -/
theorem thetaAutomorphyFactor_mul (γ₁ γ₂ : SL(2, ℤ)) (z : ℍ) :
    thetaAutomorphyFactor (γ₁ * γ₂) z =
      thetaAutomorphyFactor γ₁ (γ₂ • z) * thetaAutomorphyFactor γ₂ z := by
  rw [thetaAutomorphyFactor_def, thetaAutomorphyFactor_def, thetaAutomorphyFactor_def,
    mul_smul, div_mul_div_cancel₀ (by simpa using jacobiTheta_natCast_mul_ne_zero 2 (γ₂ • z))]

@[simp]
theorem thetaAutomorphyFactor_one (z : ℍ) : thetaAutomorphyFactor 1 z = 1 := by
  rw [thetaAutomorphyFactor_def, one_smul,
    div_self (by simpa using jacobiTheta_natCast_mul_ne_zero 2 z)]

/-- Negating the matrix leaves `thetaAutomorphyFactor` unchanged: `γ` and `-γ` have the same
automorphy factor, so it descends to `PSL(2, ℤ)`. -/
@[simp]
theorem thetaAutomorphyFactor_neg (γ : SL(2, ℤ)) (z : ℍ) :
    thetaAutomorphyFactor (-γ) z = thetaAutomorphyFactor γ z := by
  simp only [thetaAutomorphyFactor_def, ModularGroup.SL_neg_smul]

/-- Inversion formula for the theta automorphy factor:
`thetaAutomorphyFactor γ⁻¹ (γ • z) = (thetaAutomorphyFactor γ z)⁻¹`. -/
theorem thetaAutomorphyFactor_inv (γ : SL(2, ℤ)) (z : ℍ) :
    thetaAutomorphyFactor γ⁻¹ (γ • z) = (thetaAutomorphyFactor γ z)⁻¹ := by
  have h := thetaAutomorphyFactor_mul γ⁻¹ γ z
  rw [inv_mul_cancel, thetaAutomorphyFactor_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

/-- For `n : ℤ`, `ModularGroup.T ^ n` acts by `z ↦ z + n` with automorphy factor `1`. -/
@[simp]
theorem thetaAutomorphyFactor_T_zpow (n : ℤ) (z : ℍ) :
    thetaAutomorphyFactor (ModularGroup.T ^ n) z = 1 := by
  rw [thetaAutomorphyFactor_def, UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd,
    ofReal_intCast, mul_add, add_comm (2 * (n : ℂ)), mul_comm (2 : ℂ) (n : ℂ),
    (periodic_jacobiTheta_two.int_mul n) (2 * (z : ℂ)),
    div_self (by simpa using jacobiTheta_natCast_mul_ne_zero 2 z)]

/-- Unit-translation case: `ModularGroup.T` has automorphy factor `1`. -/
@[simp]
theorem thetaAutomorphyFactor_T (z : ℍ) : thetaAutomorphyFactor ModularGroup.T z = 1 := by
  simpa using thetaAutomorphyFactor_T_zpow 1 z

end TauCeti
