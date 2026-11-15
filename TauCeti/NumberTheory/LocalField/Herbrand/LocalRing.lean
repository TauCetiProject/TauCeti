/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Herbrand.Jump
public import TauCeti.RingTheory.LocalRing.Herbrand

/-!
# Agreement between local-field and local-ring Herbrand theory

For a finite Galois extension `L/K` of nonarchimedean local fields, `herbrand`, `herbrandOrderIso`,
`inverseHerbrand`, `psiNat`, `upperRamificationGroup`, and `UpperJump` in
`TauCeti.LocalFieldsRamification` agree with their `TauCeti.IsLocalRing` counterparts on `𝒪[L]`
(extending `TauCeti.NumberTheory.LocalField.RamificationGroup`). Not marked `@[simp]` so existing
`@[simp]` normal forms in `TauCeti.LocalFieldsRamification` are preserved.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §3.
-/

public section
noncomputable section

open ValuativeRel

namespace TauCeti.LocalFieldsRamification

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]
  [IsGalois K L]

/-- `herbrand` agrees with `TauCeti.IsLocalRing.herbrandFun` on `𝒪[L]`. -/
theorem coe_herbrand_eq_herbrandFun (u : RamificationIndexDomain) :
    (herbrand K L u : ℝ) = TauCeti.IsLocalRing.herbrandFun (L ≃ₐ[K] L) 𝒪[L] u := by
  simp_rw [coe_herbrand, TauCeti.IsLocalRing.herbrandFun_def,
    lowerRamificationGroupReal_eq_ramificationGroupReal, lowerRamificationGroup_def]

/-- `herbrandOrderIso` agrees with `TauCeti.IsLocalRing.herbrandOrderIso` on `𝒪[L]`. -/
theorem herbrandOrderIso_eq_isLocalRingHerbrandOrderIso :
    herbrandOrderIso K L = TauCeti.IsLocalRing.herbrandOrderIso (L ≃ₐ[K] L) 𝒪[L] :=
  OrderIso.ext <| funext fun u ↦ Subtype.ext <| by
    rw [herbrandOrderIso_apply, TauCeti.IsLocalRing.coe_herbrandOrderIso_apply,
      coe_herbrand_eq_herbrandFun]

/-- `inverseHerbrand` agrees with `TauCeti.IsLocalRing.inverseHerbrandFun` on `𝒪[L]`. -/
theorem coe_inverseHerbrand_eq_inverseHerbrandFun (v : RamificationIndexDomain) :
    (inverseHerbrand K L v : ℝ) = TauCeti.IsLocalRing.inverseHerbrandFun (L ≃ₐ[K] L) 𝒪[L] v := by
  rw [← herbrandOrderIso_symm_apply, herbrandOrderIso_eq_isLocalRingHerbrandOrderIso,
    TauCeti.IsLocalRing.coe_herbrandOrderIso_symm_apply]

/-- `psiNat` agrees with `TauCeti.IsLocalRing.psiNat` on `𝒪[L]`. -/
theorem psiNat_eq_isLocalRingPsiNat : psiNat K L = TauCeti.IsLocalRing.psiNat (L ≃ₐ[K] L) 𝒪[L] :=
  funext fun _ ↦ Nat.cast_injective (R := ℝ) <| by simp [coe_inverseHerbrand_eq_inverseHerbrandFun]

/-- `upperRamificationGroup` agrees with `TauCeti.IsLocalRing.upperRamificationGroup` on `𝒪[L]`. -/
theorem upperRamificationGroup_eq_isLocalRingUpperRamificationGroup (v : RamificationIndexDomain) :
    upperRamificationGroup K L v =
      TauCeti.IsLocalRing.upperRamificationGroup (L ≃ₐ[K] L) 𝒪[L] v := by
  rw [upperRamificationGroup_def, coe_inverseHerbrand_eq_inverseHerbrandFun,
    lowerRamificationGroupReal_eq_ramificationGroupReal,
    TauCeti.IsLocalRing.upperRamificationGroup_def]

/-- `UpperJump` agrees with `TauCeti.IsLocalRing.UpperJump` on `𝒪[L]`. -/
theorem upperJump_iff_isLocalRingUpperJump (v : RamificationIndexDomain) :
    UpperJump K L v ↔ TauCeti.IsLocalRing.UpperJump (L ≃ₐ[K] L) 𝒪[L] v := by
  rw [← lowerJump_inverseHerbrand_iff, lowerJump_iff_isLocalRingLowerJump,
    coe_inverseHerbrand_eq_inverseHerbrandFun, TauCeti.IsLocalRing.lowerJump_inverseHerbrandFun_iff]

end TauCeti.LocalFieldsRamification
