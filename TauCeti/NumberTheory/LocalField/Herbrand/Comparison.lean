/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Herbrand.Jump
public import TauCeti.RingTheory.LocalRing.Herbrand

/-!
# Comparison of local-field and local-ring Herbrand functions

For a finite extension `L / K` of nonarchimedean local fields, this file records the exact
agreement between the local-field Herbrand API in `TauCeti.LocalFieldsRamification` and the general
local-ring API in `TauCeti.IsLocalRing` specialized to `G = L ≃ₐ[K] L` and `S = 𝒪[L]`.

## Main results

* `TauCeti.LocalFieldsRamification.lowerRamificationGroupReal_eq_isLocalRing`,
  `TauCeti.LocalFieldsRamification.lowerJump_iff_isLocalRing`
* `TauCeti.LocalFieldsRamification.coe_herbrand_eq_herbrandFun`,
  `TauCeti.LocalFieldsRamification.coe_inverseHerbrand_eq_inverseHerbrandFun`,
  `TauCeti.LocalFieldsRamification.herbrandOrderIso_eq_herbrandOrderIsoIci`,
  `TauCeti.LocalFieldsRamification.psiNat_eq_isLocalRing_psiNat`
* `TauCeti.LocalFieldsRamification.upperRamificationGroup_eq_isLocalRing`,
  `TauCeti.LocalFieldsRamification.upperJump_iff_isLocalRing`
-/

public section
noncomputable section

open ValuativeRel

namespace TauCeti.LocalFieldsRamification

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Module.Finite K L]

/-- The real-indexed lower ramification groups agree with `TauCeti.IsLocalRing`. -/
theorem lowerRamificationGroupReal_eq_isLocalRing (u : ℝ) :
    lowerRamificationGroupReal K L u =
      TauCeti.IsLocalRing.ramificationGroupReal (L ≃ₐ[K] L) 𝒪[L] u := by
  rw [lowerRamificationGroupReal_def, TauCeti.IsLocalRing.ramificationGroupReal_def,
    lowerRamificationGroup_def]

/-- Lower jumps agree with `TauCeti.IsLocalRing.LowerJump` on `[-1, ∞)`. -/
theorem lowerJump_iff_isLocalRing (u : RamificationIndexDomain) :
    LowerJump K L u ↔ TauCeti.IsLocalRing.LowerJump (L ≃ₐ[K] L) 𝒪[L] u := by
  rw [lowerJump_iff, TauCeti.IsLocalRing.lowerJump_iff]
  exact ⟨fun h v huv ↦ by
      simpa only [lowerRamificationGroupReal_eq_isLocalRing] using h ⟨v, u.2.trans huv.le⟩ huv,
    fun h v huv ↦ by simpa only [lowerRamificationGroupReal_eq_isLocalRing] using h v huv⟩

variable [IsGalois K L]

/-- The local-field Herbrand function agrees with `TauCeti.IsLocalRing.herbrandFun`. -/
theorem coe_herbrand_eq_herbrandFun (u : RamificationIndexDomain) :
    (herbrand K L u : ℝ) = TauCeti.IsLocalRing.herbrandFun (L ≃ₐ[K] L) 𝒪[L] u := by
  rw [coe_herbrand, TauCeti.IsLocalRing.herbrandFun_def]
  simp_rw [lowerRamificationGroupReal_eq_isLocalRing, lowerRamificationGroup_def]

/-- The local-field inverse Herbrand function agrees with `TauCeti.IsLocalRing.inverseHerbrandFun`.
-/
theorem coe_inverseHerbrand_eq_inverseHerbrandFun (v : RamificationIndexDomain) :
    (inverseHerbrand K L v : ℝ) =
      TauCeti.IsLocalRing.inverseHerbrandFun (L ≃ₐ[K] L) 𝒪[L] v := by
  apply (TauCeti.IsLocalRing.herbrandFun_strictMono (L ≃ₐ[K] L) 𝒪[L]).injective
  rw [TauCeti.IsLocalRing.herbrandFun_inverseHerbrandFun, ← coe_herbrand_eq_herbrandFun K L,
    herbrand_inverseHerbrand]

/-- The local-field Herbrand order isomorphism equals `TauCeti.IsLocalRing.herbrandOrderIsoIci`. -/
theorem herbrandOrderIso_eq_herbrandOrderIsoIci :
    herbrandOrderIso K L = TauCeti.IsLocalRing.herbrandOrderIsoIci (L ≃ₐ[K] L) 𝒪[L] := by
  ext u
  rw [herbrandOrderIso_apply, TauCeti.IsLocalRing.coe_herbrandOrderIsoIci,
    coe_herbrand_eq_herbrandFun]

/-- The local-field integral inverse Herbrand function equals `TauCeti.IsLocalRing.psiNat`. -/
theorem psiNat_eq_isLocalRing_psiNat (n : ℕ) :
    psiNat K L n = TauCeti.IsLocalRing.psiNat (L ≃ₐ[K] L) 𝒪[L] n := by
  apply Nat.cast_injective (R := ℝ)
  rw [coe_psiNat, TauCeti.IsLocalRing.coe_psiNat, coe_inverseHerbrand_eq_inverseHerbrandFun]

/-- The local-field upper ramification groups agree with `TauCeti.IsLocalRing`. -/
theorem upperRamificationGroup_eq_isLocalRing (v : RamificationIndexDomain) :
    upperRamificationGroup K L v =
      TauCeti.IsLocalRing.upperRamificationGroup (L ≃ₐ[K] L) 𝒪[L] v := by
  rw [upperRamificationGroup_def, TauCeti.IsLocalRing.upperRamificationGroup_def,
    coe_inverseHerbrand_eq_inverseHerbrandFun, lowerRamificationGroupReal_eq_isLocalRing]

/-- Upper jumps agree with `TauCeti.IsLocalRing.UpperJump` on `[-1, ∞)`. -/
theorem upperJump_iff_isLocalRing (v : RamificationIndexDomain) :
    UpperJump K L v ↔ TauCeti.IsLocalRing.UpperJump (L ≃ₐ[K] L) 𝒪[L] v := by
  rw [upperJump_iff, TauCeti.IsLocalRing.upperJump_iff]
  exact ⟨fun h w hvw ↦ by
      simpa only [upperRamificationGroup_eq_isLocalRing] using h ⟨w, v.2.trans hvw.le⟩ hvw,
    fun h w hvw ↦ by simpa only [upperRamificationGroup_eq_isLocalRing] using h w hvw⟩

end TauCeti.LocalFieldsRamification
