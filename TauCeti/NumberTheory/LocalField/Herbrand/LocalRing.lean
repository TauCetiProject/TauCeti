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
`TauCeti.LocalFieldsRamification` agree with their `TauCeti.IsLocalRing` counterparts for
`(L ≃ₐ[K] L)` acting on `𝒪[L]` (extending the lower-filtration bridge in
`TauCeti.NumberTheory.LocalField.RamificationGroup`). These bridge lemmas are deliberately not
marked `@[simp]` so that existing `@[simp]` normal forms in `TauCeti.LocalFieldsRamification` are
preserved when this module is imported.

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

theorem coe_herbrand_eq_herbrandFun (u : RamificationIndexDomain) :
    (herbrand K L u : ℝ) = TauCeti.IsLocalRing.herbrandFun (L ≃ₐ[K] L) 𝒪[L] u := by
  simp_rw [coe_herbrand, TauCeti.IsLocalRing.herbrandFun_def,
    lowerRamificationGroupReal_eq_ramificationGroupReal, lowerRamificationGroup_def]

theorem herbrandOrderIso_eq :
    herbrandOrderIso K L = TauCeti.IsLocalRing.herbrandOrderIso (L ≃ₐ[K] L) 𝒪[L] :=
  OrderIso.ext <| funext fun u ↦ Subtype.ext <| by
    rw [herbrandOrderIso_apply, TauCeti.IsLocalRing.coe_herbrandOrderIso_apply,
      coe_herbrand_eq_herbrandFun]

theorem coe_inverseHerbrand_eq_inverseHerbrandFun (v : RamificationIndexDomain) :
    (inverseHerbrand K L v : ℝ) = TauCeti.IsLocalRing.inverseHerbrandFun (L ≃ₐ[K] L) 𝒪[L] v := by
  rw [← herbrandOrderIso_symm_apply, herbrandOrderIso_eq,
    TauCeti.IsLocalRing.coe_herbrandOrderIso_symm_apply]

theorem psiNat_eq : psiNat K L = TauCeti.IsLocalRing.psiNat (L ≃ₐ[K] L) 𝒪[L] :=
  funext fun n ↦ Nat.cast_injective (R := ℝ) <| by
    rw [coe_psiNat, TauCeti.IsLocalRing.coe_psiNat, coe_inverseHerbrand_eq_inverseHerbrandFun]

theorem upperRamificationGroup_eq (v : RamificationIndexDomain) :
    upperRamificationGroup K L v =
      TauCeti.IsLocalRing.upperRamificationGroup (L ≃ₐ[K] L) 𝒪[L] v := by
  rw [upperRamificationGroup_def, coe_inverseHerbrand_eq_inverseHerbrandFun,
    lowerRamificationGroupReal_eq_ramificationGroupReal,
    TauCeti.IsLocalRing.upperRamificationGroup_def]

theorem upperJump_iff_isLocalRingUpperJump (v : RamificationIndexDomain) :
    UpperJump K L v ↔ TauCeti.IsLocalRing.UpperJump (L ≃ₐ[K] L) 𝒪[L] v := by
  rw [← lowerJump_inverseHerbrand_iff, lowerJump_iff_isLocalRingLowerJump,
    coe_inverseHerbrand_eq_inverseHerbrandFun, TauCeti.IsLocalRing.lowerJump_inverseHerbrandFun_iff]

end TauCeti.LocalFieldsRamification
