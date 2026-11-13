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

For a finite extension `L/K` of nonarchimedean local fields, the lower ramification groups in
`TauCeti.LocalFieldsRamification` are defined directly as the `TauCeti.IsLocalRing` ramification
groups of `(L ≃ₐ[K] L)` acting on the valuation ring `𝒪[L]`. When `L/K` is Galois, the Herbrand
order isomorphism, the forward and inverse Herbrand functions, the integral inverse Herbrand
function, the upper ramification filtration, and the lower and upper break predicates in
`TauCeti.LocalFieldsRamification` agree with their local-ring counterparts in
`TauCeti.IsLocalRing` specialized to `G = (L ≃ₐ[K] L)` and `S = 𝒪[L]`.

These bridge lemmas are deliberately not marked `@[simp]` so that existing `@[simp]` normal forms in
`TauCeti.LocalFieldsRamification` are preserved when this module is imported.

## Main results

* `TauCeti.LocalFieldsRamification.lowerRamificationGroupReal_eq_isLocalRing`:
  `lowerRamificationGroupReal K L u` agrees with
  `TauCeti.IsLocalRing.ramificationGroupReal (L ≃ₐ[K] L) 𝒪[L] u`.
* `TauCeti.LocalFieldsRamification.lowerJump_iff_isLocalRing`: `LowerJump K L u` agrees with
  `TauCeti.IsLocalRing.LowerJump (L ≃ₐ[K] L) 𝒪[L] u`.
* `TauCeti.LocalFieldsRamification.coe_herbrand_eq_herbrandFun`: `(herbrand K L u : ℝ)` agrees with
  `TauCeti.IsLocalRing.herbrandFun (L ≃ₐ[K] L) 𝒪[L] u`.
* `TauCeti.LocalFieldsRamification.herbrandOrderIso_eq`: `herbrandOrderIso K L` agrees with
  `TauCeti.IsLocalRing.herbrandOrderIso (L ≃ₐ[K] L) 𝒪[L]`.
* `TauCeti.LocalFieldsRamification.coe_inverseHerbrand_eq_inverseHerbrandFun`:
  `(inverseHerbrand K L v : ℝ)` agrees with
  `TauCeti.IsLocalRing.inverseHerbrandFun (L ≃ₐ[K] L) 𝒪[L] v`.
* `TauCeti.LocalFieldsRamification.psiNat_eq`: `psiNat K L` agrees with
  `TauCeti.IsLocalRing.psiNat (L ≃ₐ[K] L) 𝒪[L]`.
* `TauCeti.LocalFieldsRamification.upperRamificationGroup_eq`: `upperRamificationGroup K L v`
  agrees with `TauCeti.IsLocalRing.upperRamificationGroup (L ≃ₐ[K] L) 𝒪[L] v`.
* `TauCeti.LocalFieldsRamification.upperJump_iff_isLocalRing`: `UpperJump K L v` agrees with
  `TauCeti.IsLocalRing.UpperJump (L ≃ₐ[K] L) 𝒪[L] v`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §3.
-/

public section
noncomputable section

open ValuativeRel

namespace TauCeti.LocalFieldsRamification

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Module.Finite K L]

/-- The real-indexed lower ramification group in `TauCeti.LocalFieldsRamification` agrees with
`TauCeti.IsLocalRing.ramificationGroupReal` on `𝒪[L]`. -/
theorem lowerRamificationGroupReal_eq_isLocalRing (u : ℝ) :
    lowerRamificationGroupReal K L u =
      TauCeti.IsLocalRing.ramificationGroupReal (L ≃ₐ[K] L) 𝒪[L] u := by
  rw [lowerRamificationGroupReal_def, lowerRamificationGroup_def,
    TauCeti.IsLocalRing.ramificationGroupReal_def]

/-- The local-field lower-break predicate agrees with the local-ring lower-break predicate on
`𝒪[L]`. -/
theorem lowerJump_iff_isLocalRing (u : RamificationIndexDomain) :
    LowerJump K L u ↔ TauCeti.IsLocalRing.LowerJump (L ≃ₐ[K] L) 𝒪[L] u := by
  rw [lowerJump_iff, TauCeti.IsLocalRing.lowerJump_iff]
  constructor
  · intro hu v huv
    simpa only [lowerRamificationGroupReal_eq_isLocalRing] using
      hu ⟨v, u.2.trans huv.le⟩ huv
  · intro hu v huv
    simpa only [lowerRamificationGroupReal_eq_isLocalRing] using hu v huv

variable [IsGalois K L]

/-- The local-field Herbrand function agrees with `TauCeti.IsLocalRing.herbrandFun` on `𝒪[L]`. -/
theorem coe_herbrand_eq_herbrandFun (u : RamificationIndexDomain) :
    (herbrand K L u : ℝ) = TauCeti.IsLocalRing.herbrandFun (L ≃ₐ[K] L) 𝒪[L] u := by
  simp_rw [coe_herbrand, TauCeti.IsLocalRing.herbrandFun_def,
    lowerRamificationGroupReal_eq_isLocalRing, lowerRamificationGroup_def]

/-- The local-field Herbrand order isomorphism on `[-1, ∞)` agrees with
`TauCeti.IsLocalRing.herbrandOrderIso` on `𝒪[L]`. -/
theorem herbrandOrderIso_eq :
    herbrandOrderIso K L = TauCeti.IsLocalRing.herbrandOrderIso (L ≃ₐ[K] L) 𝒪[L] :=
  OrderIso.ext <| funext fun u ↦ Subtype.ext <| by
    rw [herbrandOrderIso_apply, TauCeti.IsLocalRing.coe_herbrandOrderIso_apply,
      coe_herbrand_eq_herbrandFun]

/-- The local-field inverse Herbrand function agrees with
`TauCeti.IsLocalRing.inverseHerbrandFun` on `𝒪[L]`. -/
theorem coe_inverseHerbrand_eq_inverseHerbrandFun (v : RamificationIndexDomain) :
    (inverseHerbrand K L v : ℝ) =
      TauCeti.IsLocalRing.inverseHerbrandFun (L ≃ₐ[K] L) 𝒪[L] v := by
  rw [← herbrandOrderIso_symm_apply, herbrandOrderIso_eq,
    TauCeti.IsLocalRing.coe_herbrandOrderIso_symm_apply]

/-- The local-field integral inverse Herbrand function `ψℕ_{L/K}` agrees with
`TauCeti.IsLocalRing.psiNat` on `𝒪[L]`. -/
theorem psiNat_eq : psiNat K L = TauCeti.IsLocalRing.psiNat (L ≃ₐ[K] L) 𝒪[L] :=
  funext fun n ↦ Nat.cast_injective (R := ℝ) <| by
    rw [coe_psiNat, TauCeti.IsLocalRing.coe_psiNat, coe_inverseHerbrand_eq_inverseHerbrandFun]

/-- The local-field upper ramification filtration agrees with
`TauCeti.IsLocalRing.upperRamificationGroup` on `𝒪[L]`. -/
theorem upperRamificationGroup_eq (v : RamificationIndexDomain) :
    upperRamificationGroup K L v =
      TauCeti.IsLocalRing.upperRamificationGroup (L ≃ₐ[K] L) 𝒪[L] v := by
  rw [upperRamificationGroup_def, coe_inverseHerbrand_eq_inverseHerbrandFun,
    lowerRamificationGroupReal_eq_isLocalRing, TauCeti.IsLocalRing.upperRamificationGroup_def]

/-- The local-field upper-break predicate agrees with `TauCeti.IsLocalRing.UpperJump` on `𝒪[L]`. -/
theorem upperJump_iff_isLocalRing (v : RamificationIndexDomain) :
    UpperJump K L v ↔ TauCeti.IsLocalRing.UpperJump (L ≃ₐ[K] L) 𝒪[L] v := by
  rw [← lowerJump_inverseHerbrand_iff, lowerJump_iff_isLocalRing,
    coe_inverseHerbrand_eq_inverseHerbrandFun, TauCeti.IsLocalRing.lowerJump_inverseHerbrandFun_iff]

end TauCeti.LocalFieldsRamification
