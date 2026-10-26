/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Module
import Mathlib.Tactic.Module

/-!
# Localizations of modules away from an element

Let `φ : N → N_f` be a localization of a module away from `f`. If an element `σ` of `N_f` is
written as `x / fᵏ`, then annihilation of `x` by a power of `f g` transfers to annihilation of
`σ` by the same power of `g`, because the factor `f` is invertible on `N_f`. On `Spec R` this says
that a section of `M^~` over `D(f)` vanishing on `D(f g)` is killed by a power of `g`.

If multiplication by `r : R` is bijective on an `R`-module `M`, then every power of `r` acts
invertibly. Consequently the identity of `M` is a localization map at the powers of `r`, and `M`
inherits a module structure over `Localization.Away r`. This is useful when a module is described
by divisibility rather than by an existing action of the localized ring; in particular, it turns a
uniquely `r`-divisible abelian group into a module over `R[r⁻¹]`.

## Main statements

* `IsLocalizedModule.Away.pow_smul_eq_zero_of_pow_smul_eq`: if `fᵏ σ = φ x` and `(f g)ⁿ x = 0`,
  then `gⁿ σ = 0`.
* `Function.Bijective.isLocalizedModule_id_powers`: if multiplication by `r` is bijective, the
  identity is a localization map at the powers of `r`.
* `Function.Bijective.localizationAwayModule`: the induced `Localization.Away r`-module structure,
  extending the original action by `Function.Bijective.isScalarTower_localizationAwayModule`.
* `TauCeti.bijective_smul_of_localizationAwayModule`: conversely, multiplication by `r` is bijective
  on any `Localization.Away r`-module extending the `R`-action.
-/

public section

namespace IsLocalizedModule.Away

variable {A N N' : Type*} [CommSemiring A] [AddCommMonoid N] [Module A N] [AddCommMonoid N']
  [Module A N'] {f g : A} (φ : N →ₗ[A] N') [IsLocalizedModule.Away f φ]

/-- Clearing denominators in a localization `φ : N → N_f`: if `fᵏ σ = φ x` and `(f g)ⁿ` kills `x`,
then `gⁿ` kills `σ`. -/
theorem pow_smul_eq_zero_of_pow_smul_eq {x : N} {σ : N'} {k n : ℕ} (hk : f ^ k • σ = φ x)
    (hn : (f * g) ^ n • x = 0) : g ^ n • σ = 0 := by
  refine IsLocalizedModule.smul_injective φ ⟨f ^ (n + k), pow_mem (Submonoid.mem_powers f) _⟩ ?_
  simp only [Submonoid.mk_smul, smul_zero]
  have h : f ^ (n + k) • g ^ n • σ = (f * g) ^ n • f ^ k • σ := by module
  rw [h, hk, ← map_smul, hn, map_zero]

end IsLocalizedModule.Away

namespace Function.Bijective

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] {r : R}

/-- If scalar multiplication by `r` is bijective on `M`, the identity of `M` is a localization
map at the powers of `r`. -/
theorem isLocalizedModule_id_powers (h : Function.Bijective fun x : M ↦ r • x) :
    IsLocalizedModule (Submonoid.powers r) (LinearMap.id : M →ₗ[R] M) := by
  have hr : IsUnit (algebraMap R (Module.End R M) r) := by
    rw [Module.End.isUnit_iff, funext (Module.algebraMap_end_apply R R M r)]
    exact h
  exact IsLocalizedModule.Away.mk hr (fun x ↦ ⟨0, x, by simp⟩) fun _ _ hxy ↦ ⟨0, by simpa using hxy⟩

/-- The module structure over `R[r⁻¹]` on an `R`-module on which multiplication by `r` is
bijective. Its restriction to `R` is the original module structure, as recorded by
`Function.Bijective.isScalarTower_localizationAwayModule`. -/
@[instance_reducible]
noncomputable def localizationAwayModule (h : Function.Bijective fun x : M ↦ r • x) :
    Module (Localization.Away r) M := by
  let _ : IsLocalizedModule (Submonoid.powers r) (LinearMap.id : M →ₗ[R] M) :=
    h.isLocalizedModule_id_powers
  exact IsLocalizedModule.module (Submonoid.powers r) (LinearMap.id : M →ₗ[R] M)

/-- The localized scalar action supplied by `Function.Bijective.localizationAwayModule` extends
the original `R`-module structure. -/
theorem isScalarTower_localizationAwayModule (h : Function.Bijective fun x : M ↦ r • x) :
    letI : Module (Localization.Away r) M := h.localizationAwayModule
    IsScalarTower R (Localization.Away r) M := by
  let _ : IsLocalizedModule (Submonoid.powers r) (LinearMap.id : M →ₗ[R] M) :=
    h.isLocalizedModule_id_powers
  exact IsLocalizedModule.isScalarTower_module (Submonoid.powers r)
    (LinearMap.id : M →ₗ[R] M)

end Function.Bijective

namespace TauCeti

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] {r : R}

/-- Conversely, an `R[r⁻¹]`-module whose scalar action extends that of `R` has bijective scalar
multiplication by `r`. -/
theorem bijective_smul_of_localizationAwayModule [Module (Localization.Away r) M]
    [IsScalarTower R (Localization.Away r) M] :
    Function.Bijective fun x : M ↦ r • x := by
  have hloc : IsLocalizedModule (Submonoid.powers r) (LinearMap.id : M →ₗ[R] M) :=
    isLocalizedModule_id (Submonoid.powers r) M (Localization.Away r)
  have hr : r ∈ Submonoid.powers r := ⟨1, pow_one r⟩
  exact (Module.End.isUnit_iff _).mp (hloc.map_units ⟨r, hr⟩)

end TauCeti
