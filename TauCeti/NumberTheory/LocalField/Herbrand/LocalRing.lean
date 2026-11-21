/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Herbrand.Jump

/-!
# Agreement of local-field and local-ring Herbrand theory

For a finite Galois extension `L/K` of nonarchimedean local fields, the local-field Herbrand
functions `herbrand`, `inverseHerbrand`, `herbrandOrderIso`, `psiNat`, and the upper ramification
filtration `upperRamificationGroup` in `TauCeti.LocalFieldsRamification` specialize the general
local-ring definitions in `TauCeti.IsLocalRing` applied to `G = L ≃ₐ[K] L` acting on `𝒪[L]`. The
lower-jump agreement `lowerJump_iff_localRing` lives alongside `LowerJump` in
`TauCeti.NumberTheory.LocalField.RamificationGroup`.

## Main results

* `TauCeti.LocalFieldsRamification.coe_herbrand_eq_herbrandFun`:
  `(herbrand K L u : ℝ) = TauCeti.IsLocalRing.herbrandFun (L ≃ₐ[K] L) 𝒪[L] u`.
* `TauCeti.LocalFieldsRamification.herbrandOrderIso_eq_localRing`:
  `herbrandOrderIso K L = TauCeti.IsLocalRing.herbrandOrderIso (L ≃ₐ[K] L) 𝒪[L]`.
* `TauCeti.LocalFieldsRamification.coe_inverseHerbrand_eq_inverseHerbrandFun`:
  `(inverseHerbrand K L v : ℝ) = TauCeti.IsLocalRing.inverseHerbrandFun (L ≃ₐ[K] L) 𝒪[L] v`.
* `TauCeti.LocalFieldsRamification.psiNat_eq_localRing`:
  `psiNat K L n = TauCeti.IsLocalRing.psiNat (L ≃ₐ[K] L) 𝒪[L] n`.
* `TauCeti.LocalFieldsRamification.upperRamificationGroup_eq_localRing`:
  `upperRamificationGroup K L v = TauCeti.IsLocalRing.upperRamificationGroup (L ≃ₐ[K] L) 𝒪[L] v`.
* `TauCeti.LocalFieldsRamification.upperJump_iff_localRing`:
  `UpperJump K L v ↔ TauCeti.IsLocalRing.UpperJump (L ≃ₐ[K] L) 𝒪[L] v`.
-/

public section
noncomputable section

open ValuativeRel

namespace TauCeti.LocalFieldsRamification

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Module.Finite K L] [IsGalois K L]

/-- The local-field Herbrand function agrees with `TauCeti.IsLocalRing.herbrandFun` on
`[-1, ∞)`. -/
theorem coe_herbrand_eq_herbrandFun (u : RamificationIndexDomain) :
    (herbrand K L u : ℝ) = TauCeti.IsLocalRing.herbrandFun (L ≃ₐ[K] L) 𝒪[L] u := by
  rw [coe_herbrand, TauCeti.IsLocalRing.herbrandFun_def]
  congr 1 with t
  rw [lowerRamificationGroupReal_eq_localRing, lowerRamificationGroup_def]

/-- The local-field Herbrand order isomorphism equals `TauCeti.IsLocalRing.herbrandOrderIso`. -/
theorem herbrandOrderIso_eq_localRing :
    herbrandOrderIso K L = TauCeti.IsLocalRing.herbrandOrderIso (L ≃ₐ[K] L) 𝒪[L] := by
  refine OrderIso.ext (funext fun u ↦ Subtype.ext ?_)
  rw [herbrandOrderIso_apply, TauCeti.IsLocalRing.coe_herbrandOrderIso_apply]
  exact coe_herbrand_eq_herbrandFun K L u

/-- The local-field inverse Herbrand function agrees with `TauCeti.IsLocalRing.inverseHerbrandFun`
on `[-1, ∞)`. -/
theorem coe_inverseHerbrand_eq_inverseHerbrandFun (v : RamificationIndexDomain) :
    (inverseHerbrand K L v : ℝ) = TauCeti.IsLocalRing.inverseHerbrandFun (L ≃ₐ[K] L) 𝒪[L] v := by
  rw [← herbrandOrderIso_symm_apply, herbrandOrderIso_eq_localRing,
    TauCeti.IsLocalRing.coe_herbrandOrderIso_symm_apply]

/-- The local-field integral inverse Herbrand function agrees with `TauCeti.IsLocalRing.psiNat`. -/
theorem psiNat_eq_localRing (n : ℕ) :
    psiNat K L n = TauCeti.IsLocalRing.psiNat (L ≃ₐ[K] L) 𝒪[L] n := by
  apply Nat.cast_injective (R := ℝ)
  rw [coe_psiNat, TauCeti.IsLocalRing.coe_psiNat, coe_inverseHerbrand_eq_inverseHerbrandFun]

/-- The local-field upper ramification filtration agrees with
`TauCeti.IsLocalRing.upperRamificationGroup` on `[-1, ∞)`. -/
theorem upperRamificationGroup_eq_localRing (v : RamificationIndexDomain) :
    upperRamificationGroup K L v =
      TauCeti.IsLocalRing.upperRamificationGroup (L ≃ₐ[K] L) 𝒪[L] v := by
  rw [upperRamificationGroup_def, TauCeti.IsLocalRing.upperRamificationGroup_def,
    coe_inverseHerbrand_eq_inverseHerbrandFun, lowerRamificationGroupReal_eq_localRing]

/-- An upper break of a local-field extension agrees with an upper jump of `Gal(L/K)` acting on
`𝒪[L]`. -/
theorem upperJump_iff_localRing (v : RamificationIndexDomain) :
    UpperJump K L v ↔ TauCeti.IsLocalRing.UpperJump (L ≃ₐ[K] L) 𝒪[L] v := by
  rw [upperJump_iff, TauCeti.IsLocalRing.upperJump_iff]
  constructor
  · intro hv w hw
    have hw' : w ∈ RamificationIndexDomain := v.property.trans hw.le
    simpa only [upperRamificationGroup_eq_localRing] using hv ⟨w, hw'⟩ (Subtype.mk_lt_mk.2 hw)
  · intro hv w hw
    simpa only [upperRamificationGroup_eq_localRing] using hv w (Subtype.coe_lt_coe.2 hw)

end TauCeti.LocalFieldsRamification
