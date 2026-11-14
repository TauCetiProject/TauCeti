/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.GaloisClosure
public import TauCeti.FieldTheory.Galois.Restriction
public import TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
public import TauCeti.NumberTheory.LocalField.Herbrand.Basic

import TauCeti.NumberTheory.LocalField.Herbrand.UpperQuotient

/-!
# Upper ramification groups on finite Galois intermediate fields

Finite Galois intermediate fields `L : FiniteGaloisIntermediateField K Ω` of a field extension `Ω/K`
over a nonarchimedean local field `K` are the finite levels used to construct the upper ramification
filtration of `Gal(Ω/K)` (in particular on `AlgebraicClosure K` and `maximalAbelianExtension K`).
This file equips `L` with the canonical spectral-norm local-field structure induced from `K` and
reads its upper ramification groups via `TauCeti.LocalFieldsRamification.upperRamificationGroup`,
mirroring `TauCeti.LocalFieldsRamification.finiteGaloisLowerRamificationGroup` for the lower
numbering.

## Main definitions

* `TauCeti.LocalFieldsRamification.finiteGaloisUpperRamificationGroup`: the upper ramification
  group `Gal(L/K)^v` of `L : FiniteGaloisIntermediateField K Ω` equipped with the canonical
  local-field structure induced from `K`.

## Main results

* `TauCeti.LocalFieldsRamification.mem_finiteGaloisUpperRamificationGroup_iff`,
  `TauCeti.LocalFieldsRamification.finiteGaloisUpperRamificationGroup_eq`: the finite-level adapter
  agrees with `upperRamificationGroup K L v` for any compatible local-field structure on `L`.
* `TauCeti.LocalFieldsRamification.map_restrictNormalHom_finiteGaloisUpperRamificationGroup`,
  `comap_restrictNormalHom_finiteGaloisUpperRamificationGroup_antitone`:
  transition surjectivity and pullback antitonicity along `M ≤ N` in
  `FiniteGaloisIntermediateField K Ω`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §3, Proposition 14.
-/

public section
noncomputable section

open IntermediateField

namespace TauCeti.LocalFieldsRamification

variable (K Ω : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω]

/-- **Upper ramification group on a finite Galois intermediate field**, using the canonical
local-field structure induced from `K`. This is the upper-numbering counterpart of
`TauCeti.LocalFieldsRamification.finiteGaloisLowerRamificationGroup`. -/
def finiteGaloisUpperRamificationGroup
    (L : FiniteGaloisIntermediateField K Ω) (v : RamificationIndexDomain) :
    Subgroup (L ≃ₐ[K] L) :=
  letI := finiteIntermediateFieldValuativeRel K Ω L.toIntermediateField
  letI := finiteIntermediateFieldTopology K Ω L.toIntermediateField
  letI := finiteIntermediateField_isNonarchimedeanLocalField K Ω L.toIntermediateField
  letI := finiteIntermediateField_valuativeExtension K Ω L.toIntermediateField
  upperRamificationGroup K L v

/-- The finite-level adapter is `upperRamificationGroup K L v` on the induced local-field
structure. -/
theorem finiteGaloisUpperRamificationGroup_def
    (L : FiniteGaloisIntermediateField K Ω) (v : RamificationIndexDomain) :
    by
      letI := finiteIntermediateFieldValuativeRel K Ω L.toIntermediateField
      letI := finiteIntermediateFieldTopology K Ω L.toIntermediateField
      haveI := finiteIntermediateField_isNonarchimedeanLocalField K Ω L.toIntermediateField
      haveI := finiteIntermediateField_valuativeExtension K Ω L.toIntermediateField
      exact finiteGaloisUpperRamificationGroup K Ω L v = upperRamificationGroup K L v :=
  (rfl)

/-- Membership in the finite-level adapter is membership in `upperRamificationGroup K L v` for the
induced local-field structure. -/
@[simp]
theorem mem_finiteGaloisUpperRamificationGroup_iff
    {L : FiniteGaloisIntermediateField K Ω} {v : RamificationIndexDomain} {σ : L ≃ₐ[K] L} :
    by
      letI := finiteIntermediateFieldValuativeRel K Ω L.toIntermediateField
      letI := finiteIntermediateFieldTopology K Ω L.toIntermediateField
      haveI := finiteIntermediateField_isNonarchimedeanLocalField K Ω L.toIntermediateField
      haveI := finiteIntermediateField_valuativeExtension K Ω L.toIntermediateField
      exact σ ∈ finiteGaloisUpperRamificationGroup K Ω L v ↔
        σ ∈ upperRamificationGroup K L v := by
  rw [finiteGaloisUpperRamificationGroup_def]

/-- On any finite Galois intermediate field `L` of `Ω/K`, `finiteGaloisUpperRamificationGroup`
agrees with `upperRamificationGroup K L v` for any compatible local-field structure on `L`. -/
theorem finiteGaloisUpperRamificationGroup_eq
    (L : IntermediateField K Ω) [Module.Finite K L] [IsGalois K L]
    [vr : ValuativeRel L] [ts : TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [ValuativeExtension K L] (v : RamificationIndexDomain) :
    finiteGaloisUpperRamificationGroup K Ω ⟨L⟩ v = upperRamificationGroup K L v := by
  have hvr : finiteIntermediateFieldValuativeRel K Ω L = vr := by
    let _ := finiteIntermediateFieldValuativeRel K Ω L
    have := finiteIntermediateField_valuativeExtension K Ω L
    exact (algebraicExtensionValuativeRel_eq K L).symm.trans
      (@algebraicExtensionValuativeRel_eq K _ _ _ _ L _ _ _ vr _)
  have hts : finiteIntermediateFieldTopology K Ω L = ts := by
    let _ := finiteIntermediateFieldValuativeRel K Ω L
    let _ := finiteIntermediateFieldTopology K Ω L
    have := finiteIntermediateField_valuativeExtension K Ω L
    have := finiteIntermediateField_isValuativeTopology K Ω L
    exact (algebraicExtensionNormedFieldTopology_eq K L).symm.trans
      (@algebraicExtensionNormedFieldTopology_eq K _ _ _ _ L _ _ _ vr _ ts _)
  rw [finiteGaloisUpperRamificationGroup_def]
  subst hvr hts
  rfl

/-- Every finite-level upper ramification group `Gal(L/K)^v` is normal in `Gal(L/K)`. -/
instance instNormalFiniteGaloisUpperRamificationGroup
    (L : FiniteGaloisIntermediateField K Ω) (v : RamificationIndexDomain) :
    (finiteGaloisUpperRamificationGroup K Ω L v).Normal := by
  let _ := finiteIntermediateFieldValuativeRel K Ω L.toIntermediateField
  let _ := finiteIntermediateFieldTopology K Ω L.toIntermediateField
  have := finiteIntermediateField_isNonarchimedeanLocalField K Ω L.toIntermediateField
  have := finiteIntermediateField_valuativeExtension K Ω L.toIntermediateField
  rw [finiteGaloisUpperRamificationGroup_def]
  infer_instance

/-- For each `L : FiniteGaloisIntermediateField K Ω`, the upper ramification filtration is
decreasing. -/
theorem finiteGaloisUpperRamificationGroup_antitone (L : FiniteGaloisIntermediateField K Ω) :
    Antitone (finiteGaloisUpperRamificationGroup K Ω L) := by
  let _ := finiteIntermediateFieldValuativeRel K Ω L.toIntermediateField
  let _ := finiteIntermediateFieldTopology K Ω L.toIntermediateField
  have := finiteIntermediateField_isNonarchimedeanLocalField K Ω L.toIntermediateField
  have := finiteIntermediateField_valuativeExtension K Ω L.toIntermediateField
  intro v w hvw
  rw [finiteGaloisUpperRamificationGroup_def, finiteGaloisUpperRamificationGroup_def]
  exact upperRamificationGroup_antitone K L hvw

/-- **Transition surjectivity for `finiteGaloisUpperRamificationGroup`.** For `M ≤ N` in
`FiniteGaloisIntermediateField K Ω`, restriction along the inclusion `M →ₐ[K] N` maps `Gal(N/K)^v`
onto `Gal(M/K)^v`. -/
theorem map_restrictNormalHom_finiteGaloisUpperRamificationGroup
    {M N : FiniteGaloisIntermediateField K Ω} (hMN : M ≤ N) (v : RamificationIndexDomain) :
    (finiteGaloisUpperRamificationGroup K Ω N v).map
        (inclusion ((FiniteGaloisIntermediateField.le_iff M N).1 hMN)).restrictNormalHom =
      finiteGaloisUpperRamificationGroup K Ω M v := by
  let _ := finiteIntermediateFieldValuativeRel K Ω M.toIntermediateField
  let _ := finiteIntermediateFieldTopology K Ω M.toIntermediateField
  have := finiteIntermediateField_isNonarchimedeanLocalField K Ω M.toIntermediateField
  have := finiteIntermediateField_valuativeExtension K Ω M.toIntermediateField
  let _ := finiteIntermediateFieldValuativeRel K Ω N.toIntermediateField
  let _ := finiteIntermediateFieldTopology K Ω N.toIntermediateField
  have := finiteIntermediateField_isNonarchimedeanLocalField K Ω N.toIntermediateField
  have := finiteIntermediateField_valuativeExtension K Ω N.toIntermediateField
  let ι : M.toIntermediateField →ₐ[K] N.toIntermediateField :=
    inclusion ((FiniteGaloisIntermediateField.le_iff M N).1 hMN)
  let _ : Algebra M.toIntermediateField N.toIntermediateField := ι.toRingHom.toAlgebra
  have : IsScalarTower K M.toIntermediateField N.toIntermediateField :=
    .of_algebraMap_eq fun x ↦ (ι.commutes x).symm
  have : ValuativeExtension M.toIntermediateField N.toIntermediateField := ι.valuativeExtension
  have : Module.Finite M.toIntermediateField N.toIntermediateField :=
    .of_restrictScalars_finite K M.toIntermediateField N.toIntermediateField
  have hι : inclusion ((FiniteGaloisIntermediateField.le_iff M N).1 hMN) =
      IsScalarTower.toAlgHom K M.toIntermediateField N.toIntermediateField :=
    AlgHom.ext fun _ ↦ rfl
  rw [finiteGaloisUpperRamificationGroup_def, finiteGaloisUpperRamificationGroup_def, hι,
    AlgHom.restrictNormalHom_toAlgHom,
    map_restrictNormalHom_upperRamificationGroup K M.toIntermediateField N.toIntermediateField v]

/-- Pulling back `finiteGaloisUpperRamificationGroup K Ω M v` along restriction from `Gal(Ω/K)` is
antitone in `M : FiniteGaloisIntermediateField K Ω`. -/
theorem comap_restrictNormalHom_finiteGaloisUpperRamificationGroup_antitone
    (v : RamificationIndexDomain) :
    Antitone fun M : FiniteGaloisIntermediateField K Ω ↦
      (finiteGaloisUpperRamificationGroup K Ω M v).comap
        (AlgEquiv.restrictNormalHom (K₁ := Ω) M.toIntermediateField) := by
  intro M N hMN σ hσ
  rw [Subgroup.mem_comap, ← map_restrictNormalHom_finiteGaloisUpperRamificationGroup K Ω hMN v]
  refine ⟨AlgEquiv.restrictNormalHom N.toIntermediateField σ, hσ, ?_⟩
  rw [← IntermediateField.restrictNormalHom_val N.toIntermediateField,
    ← IntermediateField.restrictNormalHom_val M.toIntermediateField,
    AlgHom.restrictNormalHom_restrictNormalHom]
  rfl

end TauCeti.LocalFieldsRamification
