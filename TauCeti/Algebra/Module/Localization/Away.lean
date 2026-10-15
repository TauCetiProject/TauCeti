/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Module

/-!
# Modules on which one element acts invertibly

If multiplication by `r : R` is bijective on an `R`-module `M`, then every power of `r` acts
invertibly. Consequently the identity of `M` is a localization map at the powers of `r`, and `M`
inherits a module structure over `Localization.Away r`.

The construction is useful when a module is described by divisibility rather than by an existing
action of the localized ring. In particular, it turns a uniquely `r`-divisible abelian group into
a module over `R[r⁻¹]`.
-/

public section

noncomputable section

namespace TauCeti

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] {r : R}

/-- If scalar multiplication by `r` is bijective on `M`, the identity of `M` is a localization
map at the powers of `r`. -/
theorem isLocalizedModule_id_powers_of_bijective
    (h : Function.Bijective fun x : M ↦ r • x) :
    IsLocalizedModule (Submonoid.powers r) (LinearMap.id : M →ₗ[R] M) := by
  have hr : IsUnit (algebraMap R (Module.End R M) r) := by
    rw [Module.End.isUnit_iff]
    change Function.Bijective fun x : M ↦ r • x
    exact h
  refine
    { map_units := fun s ↦ ?_
      surj := fun x ↦ ⟨(x, 1), by simp⟩
      exists_of_eq := fun hxy ↦ ⟨1, by simpa using hxy⟩ }
  obtain ⟨n, hn⟩ := s.property
  rw [← hn, map_pow]
  exact hr.pow n

/-- The module structure over `R[r⁻¹]` on an `R`-module on which multiplication by `r` is
bijective. Its restriction to `R` is the original module structure, as recorded by
`isScalarTower_localizationAwayModuleOfBijective`. -/
@[instance_reducible]
def localizationAwayModuleOfBijective (h : Function.Bijective fun x : M ↦ r • x) :
    Module (Localization.Away r) M := by
  let _ : IsLocalizedModule (Submonoid.powers r) (LinearMap.id : M →ₗ[R] M) :=
    isLocalizedModule_id_powers_of_bijective h
  exact IsLocalizedModule.module (Submonoid.powers r) (LinearMap.id : M →ₗ[R] M)

/-- The localized scalar action supplied by `localizationAwayModuleOfBijective` extends the
original `R`-module structure. -/
theorem isScalarTower_localizationAwayModuleOfBijective
    (h : Function.Bijective fun x : M ↦ r • x) :
    letI : Module (Localization.Away r) M := localizationAwayModuleOfBijective h
    IsScalarTower R (Localization.Away r) M := by
  let _ : IsLocalizedModule (Submonoid.powers r) (LinearMap.id : M →ₗ[R] M) :=
    isLocalizedModule_id_powers_of_bijective h
  exact IsLocalizedModule.isScalarTower_module (Submonoid.powers r)
    (LinearMap.id : M →ₗ[R] M)

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

end
