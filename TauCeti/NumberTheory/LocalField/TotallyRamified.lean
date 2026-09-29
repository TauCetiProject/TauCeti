/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.InertiaDegree
import TauCeti.NumberTheory.LocalField.PowerSubgroup.Basic

/-!
# Total ramification in towers, and units of totally ramified extensions

The residue-degree characterization of total ramification and multiplicativity of residue degree
show that a tower is totally ramified exactly when each step is. The predicate and characterization
are defined in `RamificationIndex` and `InertiaDegree`, respectively. Since the residue fields of a
totally ramified extension agree, units of the larger ring of integers are units of the smaller one
up to principal units, and hence up to `n`-th powers for every `n` invertible in `𝒪[L]`.

## Main results

* `TauCeti.isTotallyRamified_tower_iff`: total ramification is equivalent to total ramification
  of both steps of a tower.
* `TauCeti.IsTotallyRamified.exists_eq_algebraMap_mul_pow`: in a totally ramified extension,
  every unit of `𝒪[L]` is a unit of `𝒪[K]` times the `n`-th power of a unit of `𝒪[L]`, for every
  `n` invertible in `𝒪[L]`.

## References

* J.-P. Serre, *Corps Locaux*, Chapter I, §4.
-/

public section
noncomputable section

namespace TauCeti

variable {K L : Type*} [Field K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension K L]

section Tower

variable (K L) (M : Type*) [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [ValuativeExtension L M]

/-- A tower is totally ramified exactly when both of its steps are totally ramified. -/
theorem isTotallyRamified_tower_iff :
    letI : ValuativeExtension K M := ValuativeExtension.trans K L M
    IsTotallyRamified K M ↔ IsTotallyRamified K L ∧ IsTotallyRamified L M := by
  let _ : ValuativeExtension K M := ValuativeExtension.trans K L M
  simp only [isTotallyRamified_iff_inertiaDegree_eq_one,
    inertiaDegree_tower (K := K) (L := L) M, mul_eq_one]

/-- Total ramification is transitive in a tower. -/
theorem IsTotallyRamified.trans (hKL : IsTotallyRamified K L)
    (hLM : IsTotallyRamified L M) :
    letI : ValuativeExtension K M := ValuativeExtension.trans K L M
    IsTotallyRamified K M :=
  (isTotallyRamified_tower_iff K L M).2 ⟨hKL, hLM⟩

/-- The first step of a totally ramified tower is totally ramified. -/
theorem IsTotallyRamified.tower_bot
    (hKM : letI : ValuativeExtension K M := ValuativeExtension.trans K L M
      IsTotallyRamified K M) :
    IsTotallyRamified K L :=
  ((isTotallyRamified_tower_iff K L M).1 hKM).1

/-- The second step of a totally ramified tower is totally ramified. -/
theorem IsTotallyRamified.tower_top
    (hKM : letI : ValuativeExtension K M := ValuativeExtension.trans K L M
      IsTotallyRamified K M) :
    IsTotallyRamified L M :=
  ((isTotallyRamified_tower_iff K L M).1 hKM).2

end Tower

section Units

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField

/-- In a totally ramified extension of nonarchimedean local fields, every unit of `𝒪[L]` is the
image of a unit of `𝒪[K]` times the `n`-th power of a unit of `𝒪[L]`, for every `n` invertible
in `𝒪[L]`. -/
theorem IsTotallyRamified.exists_eq_algebraMap_mul_pow (h : IsTotallyRamified K L) {n : ℕ}
    (hn : IsUnit (n : 𝒪[L])) (u : 𝒪[L]ˣ) :
    ∃ (a : 𝒪[K]ˣ) (w : 𝒪[L]ˣ), (u : 𝒪[L]) = algebraMap 𝒪[K] 𝒪[L] a * w ^ n := by
  -- the residue of `u` comes from a unit `a` of `𝒪[K]`, since the residue fields agree
  obtain ⟨c, hc⟩ :=
    (isTotallyRamified_iff_surjective_algebraMap_residueField K L).1 h (residue 𝒪[L] u)
  obtain ⟨a, rfl⟩ := residue_surjective c
  rw [ResidueField.algebraMap_residue] at hc
  have ha : IsUnit (algebraMap 𝒪[K] 𝒪[L] a) := by
    rw [← notMem_maximalIdeal, ← residue_eq_zero_iff, hc, residue_eq_zero_iff,
      notMem_maximalIdeal]
    exact u.isUnit
  -- the quotient `y = u / a` is a principal unit, hence the `n`-th power of a principal unit
  set y : 𝒪[L]ˣ := u * ha.unit⁻¹ with hy
  have hy1 : Units.map (Subring.subtype 𝒪[L] : 𝒪[L] →* L) y ∈ unitFiltration L 1 := by
    rw [mem_unitFiltration_one_iff_residue_eq_one]
    simp [hy, ← hc, (ha.map (residue 𝒪[L])).ne_zero]
  obtain ⟨⟨w, hw⟩, hwy⟩ := (powMonoidHom_unitFiltration_succ_bijective_of_isUnit hn 0).2 ⟨_, hy1⟩
  let w' := unitFiltrationToIntegerUnits 1 ⟨w, hw⟩
  refine ⟨(isUnit_of_map_unit _ _ ha).unit, w', ?_⟩
  have hwy' : w' ^ n = y := by
    apply Units.map_injective (f := (Subring.subtype 𝒪[L] : 𝒪[L] →* L)) Subtype.coe_injective
    rw [map_pow, unitsMap_subtype_unitFiltrationToIntegerUnits]
    exact Subtype.ext_iff.1 hwy
  rw [← Units.val_pow_eq_pow_val, hwy', IsUnit.unit_spec, ← ha.unit_spec, ← Units.val_mul, hy,
    mul_comm, inv_mul_cancel_right]

end Units

end TauCeti
