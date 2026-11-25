/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
public import Mathlib.RingTheory.Finiteness.Projective
public import TauCeti.Logic.Function.Basic

/-!
# Exterior powers of the dual of a finite projective module

Mathlib's pairing `exteriorPower.pairingDual R M n : ⋀ⁿ (M^*) →ₗ[R] (⋀ⁿ M)^*` sends
`φ₁ ∧ ⋯ ∧ φₙ` to the form `v₁ ∧ ⋯ ∧ vₙ ↦ det (φⱼ vᵢ)`, and Mathlib proves it bijective for finite
free modules (`exteriorPower.bijective_pairingDual`). This file shows that it is bijective for every
finite projective module, that is, for every finite locally free module, which need not be free.

The pairing is natural: for `f : M →ₗ[R] N`, pulling back along `⋀ⁿ f` after pairing is pairing
after `⋀ⁿ (f^*)` (`exteriorPower.pairingDual_comp_map_dualMap`). A finite projective module `M` is
a retract of a finite free module `F` (`Module.Finite.exists_comp_eq_id_of_projective`), and by
naturality the pairing of `M` is then a retract of the pairing of `F`, which is bijective.

In top degree `n = r` for a module of constant rank `r` this is the identification
`det (M^*) ≃ (det M)^*` of the determinant of the dual with the dual of the determinant.

## Main declarations

* `exteriorPower.pairingDual_comp_map_dualMap`: naturality of the pairing.
* `exteriorPower.bijective_pairingDual_of_projective`: the pairing is bijective for finite
  projective modules.
* `exteriorPower.pairingDualEquiv`: the resulting isomorphism `⋀ⁿ (M^*) ≃ₗ[R] (⋀ⁿ M)^*`.

## References

* N. Bourbaki, *Algebra I*, Chapter III, §11 (duality in the exterior algebra of
  finite projective modules).
-/

public section

noncomputable section

open Module

namespace exteriorPower

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- **Naturality of the exterior power pairing.** For `f : M →ₗ[R] N`, pairing `⋀ⁿ (f^*) ω` with
`⋀ⁿ M` is pairing `ω` with `⋀ⁿ N` after `⋀ⁿ f`. -/
theorem pairingDual_comp_map_dualMap (n : ℕ) (f : M →ₗ[R] N) :
    pairingDual R M n ∘ₗ map n f.dualMap = (map n f).dualMap ∘ₗ pairingDual R N n := by
  refine linearMap_ext (AlternatingMap.ext fun φ ↦ linearMap_ext (AlternatingMap.ext fun v ↦ ?_))
  simp [Function.comp_def]

/-- **The exterior power pairing of a finite projective module is perfect**: `⋀ⁿ (M^*)` is the
dual of `⋀ⁿ M` through `φ₁ ∧ ⋯ ∧ φₙ ↦ (v₁ ∧ ⋯ ∧ vₙ ↦ det (φⱼ vᵢ))`. This extends Mathlib's
`exteriorPower.bijective_pairingDual` from finite free to finite projective modules. -/
theorem bijective_pairingDual_of_projective [Module.Finite R M] [Module.Projective R M] (n : ℕ) :
    Function.Bijective (pairingDual R M n) := by
  -- `M` is a retract `p ∘ₗ s = id` of `F = Fin k → R`, and so is the pairing of `M` of that of
  -- `F` by naturality.
  obtain ⟨k, p, s, -, -, hps⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  refine Function.bijective_of_retract (a := map n p.dualMap) (b := (map n p).dualMap)
    (c := map n s.dualMap) (d := (map n s).dualMap) (bijective_pairingDual R (Fin k → R) n)
    (LinearMap.congr_fun (pairingDual_comp_map_dualMap n p))
    (LinearMap.congr_fun (pairingDual_comp_map_dualMap n s)) (fun x ↦ ?_) (fun φ ↦ ?_) <;>
  simp [← LinearMap.comp_apply, ← map_comp, LinearMap.dualMap_comp_dualMap, hps]

variable (R M) in
/-- **The exterior power of the dual of a finite projective module is the dual of its exterior
power**: `⋀ⁿ (M^*) ≃ (⋀ⁿ M)^*`, sending `φ₁ ∧ ⋯ ∧ φₙ` to `v₁ ∧ ⋯ ∧ vₙ ↦ det (φⱼ vᵢ)`
(`exteriorPower.pairingDualEquiv_ιMulti_ιMulti`). In top degree this is `det (M^*) ≃ (det M)^*`. -/
def pairingDualEquiv [Module.Finite R M] [Module.Projective R M] (n : ℕ) :
    ⋀[R]^n (Dual R M) ≃ₗ[R] Dual R (⋀[R]^n M) :=
  .ofBijective _ (bijective_pairingDual_of_projective n)

/-- The isomorphism `exteriorPower.pairingDualEquiv` is the pairing `exteriorPower.pairingDual`. -/
@[simp]
theorem coe_pairingDualEquiv [Module.Finite R M] [Module.Projective R M] (n : ℕ) :
    ⇑(pairingDualEquiv R M n) = pairingDual R M n :=
  (rfl)

/-- The linear map underlying `exteriorPower.pairingDualEquiv` is the pairing
`exteriorPower.pairingDual`. -/
@[simp]
theorem toLinearMap_pairingDualEquiv [Module.Finite R M] [Module.Projective R M] (n : ℕ) :
    (pairingDualEquiv R M n).toLinearMap = pairingDual R M n :=
  (rfl)

/-- `exteriorPower.pairingDualEquiv` pairs `φ₁ ∧ ⋯ ∧ φₙ` with `v₁ ∧ ⋯ ∧ vₙ` to `det (φⱼ vᵢ)`. -/
theorem pairingDualEquiv_ιMulti_ιMulti [Module.Finite R M] [Module.Projective R M] {n : ℕ}
    (φ : Fin n → Dual R M) (v : Fin n → M) :
    pairingDualEquiv R M n (ιMulti R n φ) (ιMulti R n v) = (Matrix.of fun i j ↦ φ j (v i)).det := by
  rw [coe_pairingDualEquiv, pairingDual_ιMulti_ιMulti]

end exteriorPower
