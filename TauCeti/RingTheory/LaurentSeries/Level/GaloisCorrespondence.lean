/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Level.Kummer
public import TauCeti.RingTheory.LaurentSeries.RamificationIndex

/-!
# Galois correspondence on a ramified level

Let `K` be a field and `n ∣ m` positive integers. The level-`m` subfield `K⸨t ^ (1 / m)⸩` of the
Puiseux field contains the level-`n` subfield `K⸨t ^ (1 / n)⸩`, and the `m`-th roots of unity `η`
of `K` act on level `m` by the Kummer automorphisms `t ^ (1 / m) ↦ η t ^ (1 / m)`
(`TauCeti.puiseuxField.levelKummer`). Such an automorphism fixes level `n` exactly when
`η ^ (m / n) = 1`, and the fixed field of a primitive `(m / n)`-th root of unity is level `n`
(`TauCeti.puiseuxField.levelKummer_mem_fixingSubgroup_restrict_iff` and
`TauCeti.puiseuxField.fixedField_zpowers_levelKummer`). This file identifies the fixed field of
all `(m / n)`-th roots of unity at once, the kernel of the power map `η ↦ η ^ (m / n)`.

When `K` contains a primitive `m`-th root of unity, level `m` is a cyclic Galois extension of
`K⸨X⸩` with group `μₘ(K)` (`TauCeti.puiseuxField.levelGalEquivRootsOfUnity`). The Galois
correspondence then identifies the subgroup fixing level `n` with the `(m / n)`-th roots of unity,
and since every intermediate field of level `m` is the level of its degree
(`TauCeti.puiseuxField.eq_restrict_level_of_finrank_eq`), every intermediate field of level `m`
over `K⸨X⸩` is a level `n` with `n ∣ m`. Ordering the positive integers by divisibility
(`TauCeti.RamificationIndex`), this is an order isomorphism between the divisors of `m` and the
intermediate fields of level `m`.

## Main definitions

* `TauCeti.puiseuxField.restrictLevelOrderIso K m`: when `K` contains a primitive `m`-th root of
  unity, the order isomorphism `n ↦ level n` from the divisors of `m`, ordered by divisibility, to
  the intermediate fields of level `m` over `K⸨X⸩`.

## Main results

* `TauCeti.puiseuxField.fixedField_map_ker_levelKummer`: if `K` has enough `(m / n)`-th roots of
  unity, the fixed field in level `m` of all `(m / n)`-th roots of unity is level `n`.
* `TauCeti.puiseuxField.finrank_restrict_level`: level `n` has degree `n` over `K⸨X⸩` as an
  intermediate field of level `m`.
* `TauCeti.puiseuxField.fixingSubgroup_restrict_level` and
  `TauCeti.puiseuxField.mem_fixingSubgroup_restrict_level_iff`: with a primitive `m`-th root of
  unity in `K`, the automorphisms of level `m` fixing level `n` are the Kummer automorphisms of the
  `(m / n)`-th roots of unity.
* `TauCeti.puiseuxField.exists_eq_restrict_level`: with a primitive `m`-th root of unity in `K`,
  every intermediate field of level `m` is a level `n` with `n ∣ m`.
-/

public section

open IntermediateField Module
open scoped LaurentSeries

namespace TauCeti.puiseuxField

variable {K : Type*} [Field K] {n m : ℕ+}

/-- **Fixed field of the `(m / n)`-th roots of unity.** For `n ∣ m`, if `K` has enough
`(m / n)`-th roots of unity, then the series of level `m` fixed by the Kummer automorphisms of all
`(m / n)`-th roots of unity, the kernel of the power map `η ↦ η ^ (m / n)` from `μₘ(K)` to
`μₙ(K)`, form level `n`. -/
theorem fixedField_map_ker_levelKummer (h : n ∣ m) [HasEnoughRootsOfUnity K ((m : ℕ) / n)] :
    fixedField ((rootsOfUnityPowOfDvd (M := K) (PNat.dvd_iff.mp h)).ker.map (levelKummer K m)) =
      restrict (level_le_level_of_dvd K h) := by
  have : NeZero ((m : ℕ) / n) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd m.pos (PNat.dvd_iff.mp h)) n.pos).ne'⟩
  obtain ⟨ω, hω⟩ := exists_rootsOfUnity_isPrimitiveRoot_of_dvd (M := K)
    (Nat.div_dvd_of_dvd (PNat.dvd_iff.mp h))
  refine le_antisymm ?_ ?_
  · rw [← fixedField_zpowers_levelKummer h hω]
    exact fixedField_le (Subgroup.zpowers_le.mpr
      ⟨ω, (mem_ker_rootsOfUnityPowOfDvd_iff _).mpr hω.pow_eq_one, rfl⟩)
  · rw [le_fixedField_iff_le_fixingSubgroup, Subgroup.map_le_iff_le_comap]
    exact fun η hη ↦ (levelKummer_mem_fixingSubgroup_restrict_iff h η).mpr
      ((mem_ker_rootsOfUnityPowOfDvd_iff _).mp hη)

/-- For `n ∣ m`, level `n` has degree `n` over `K⸨X⸩`, as an intermediate field of level `m`. -/
theorem finrank_restrict_level (h : n ∣ m) :
    finrank K⸨X⸩ (restrict (level_le_level_of_dvd K h)) = n := by
  rw [← (restrictAlgEquiv _).toLinearEquiv.finrank_eq, level_finrank]

/-- For `n ∣ m` and `n' ∣ m`, level `n` is contained in level `n'`, as intermediate fields of
level `m`, exactly when `n ∣ n'`. -/
@[simp]
theorem restrict_level_le_restrict_level_iff {n' : ℕ+} (h : n ∣ m) (h' : n' ∣ m) :
    restrict (level_le_level_of_dvd K h) ≤ restrict (level_le_level_of_dvd K h') ↔ n ∣ n' := by
  rw [← level_le_level_iff K]
  refine ⟨fun hle x hx ↦ ?_, fun hle x hx ↦ ?_⟩
  · exact (mem_restrict _ ⟨x, level_le_level_of_dvd K h hx⟩).mp (hle ((mem_restrict _ _).mpr hx))
  · exact (mem_restrict _ x).mpr (hle ((mem_restrict _ x).mp hx))

section Galois

variable [HasEnoughRootsOfUnity K m]

/-- **Fixing subgroups.** For `n ∣ m`, if `K` contains a primitive `m`-th root of unity, then the
automorphisms of level `m` over `K⸨X⸩` fixing level `n` are the Kummer automorphisms of the
`(m / n)`-th roots of unity. -/
theorem fixingSubgroup_restrict_level (h : n ∣ m) :
    fixingSubgroup (restrict (level_le_level_of_dvd K h)) =
      (rootsOfUnityPowOfDvd (M := K) (PNat.dvd_iff.mp h)).ker.map (levelKummer K m) := by
  have : FiniteDimensional K⸨X⸩ (level K m) := (levelPowerBasis K m).finite
  have : HasEnoughRootsOfUnity K ((m : ℕ) / n) :=
    .of_dvd K (Nat.div_dvd_of_dvd (PNat.dvd_iff.mp h))
  rw [← fixedField_map_ker_levelKummer h, fixingSubgroup_fixedField]

/-- For `n ∣ m`, if `K` contains a primitive `m`-th root of unity, then an automorphism `σ` of
level `m` over `K⸨X⸩` fixes level `n` exactly when the root of unity `η` attached to it satisfies
`η ^ (m / n) = 1`. -/
theorem mem_fixingSubgroup_restrict_level_iff (h : n ∣ m) (σ : Gal(level K m/K⸨X⸩)) :
    σ ∈ fixingSubgroup (restrict (level_le_level_of_dvd K h)) ↔
      ((levelGalEquivRootsOfUnity K m σ : Kˣ) : K) ^ ((m : ℕ) / n) = 1 := by
  have hk : levelKummer K m = (levelGalEquivRootsOfUnity K m).symm.toMonoidHom :=
    MonoidHom.ext fun η ↦ (levelGalEquivRootsOfUnity_symm_apply K m η).symm
  rw [fixingSubgroup_restrict_level h, hk, Subgroup.mem_map_equiv, MulEquiv.symm_symm,
    mem_ker_rootsOfUnityPowOfDvd_iff, ← Units.val_pow_eq_pow_val, Units.val_eq_one]

/-- If `K` contains a primitive `m`-th root of unity, then every intermediate field of level `m`
over `K⸨X⸩` is a level `n` with `n ∣ m`, namely the level of its degree. -/
theorem exists_eq_restrict_level (E : IntermediateField K⸨X⸩ (level K m)) :
    ∃ (n : ℕ+) (h : n ∣ m), E = restrict (level_le_level_of_dvd K h) := by
  have : FiniteDimensional K⸨X⸩ (level K m) := (levelPowerBasis K m).finite
  have hdvd : finrank K⸨X⸩ E ∣ m := by
    rw [← level_finrank K m, ← finrank_mul_finrank K⸨X⸩ E (level K m)]
    exact dvd_mul_right _ _
  have hpos : 0 < finrank K⸨X⸩ E := finrank_pos
  have hn : (finrank K⸨X⸩ E).toPNat' ∣ m := by rwa [PNat.dvd_iff, PNat.toPNat'_coe hpos]
  exact ⟨_, hn, eq_restrict_level_of_finrank_eq hn (PNat.toPNat'_coe hpos).symm⟩

variable (K m) in
/-- **Galois correspondence on a level.** If `K` contains a primitive `m`-th root of unity, then
`n ↦ level n` is an order isomorphism from the divisors `n` of `m`, ordered by divisibility, to the
intermediate fields of level `m` over `K⸨X⸩`. The inverse sends an intermediate field to its
degree (`TauCeti.puiseuxField.coe_toPNat_restrictLevelOrderIso_symm`). -/
noncomputable def restrictLevelOrderIso :
    Set.Iic (⟨m⟩ : RamificationIndex) ≃o IntermediateField K⸨X⸩ (level K m) :=
  OrderIso.ofSurjective
    (OrderEmbedding.ofMapLEIff
      (fun n ↦ restrict (level_le_level_of_dvd K (RamificationIndex.le_iff_dvd.mp n.2)))
      fun a b ↦ (restrict_level_le_restrict_level_iff (RamificationIndex.le_iff_dvd.mp a.2)
        (RamificationIndex.le_iff_dvd.mp b.2)).trans
        (RamificationIndex.le_iff_dvd.symm.trans Subtype.coe_le_coe))
    fun E ↦ by
      obtain ⟨n, h, rfl⟩ := exists_eq_restrict_level E
      exact ⟨⟨⟨n⟩, RamificationIndex.le_iff_dvd.mpr h⟩, rfl⟩

/-- The Galois correspondence on level `m` sends a divisor `n` of `m` to level `n`. -/
@[simp]
theorem restrictLevelOrderIso_apply (n : Set.Iic (⟨m⟩ : RamificationIndex)) :
    restrictLevelOrderIso K m n =
      restrict (level_le_level_of_dvd K (RamificationIndex.le_iff_dvd.mp n.2)) :=
  (rfl)

/-- The inverse of the Galois correspondence on level `m` sends an intermediate field to its
degree over `K⸨X⸩`. -/
@[simp]
theorem coe_toPNat_restrictLevelOrderIso_symm (E : IntermediateField K⸨X⸩ (level K m)) :
    (((restrictLevelOrderIso K m).symm E : RamificationIndex).toPNat : ℕ) = finrank K⸨X⸩ E := by
  conv_rhs => rw [← (restrictLevelOrderIso K m).apply_symm_apply E]
  rw [restrictLevelOrderIso_apply]
  exact (finrank_restrict_level
    (RamificationIndex.le_iff_dvd.mp ((restrictLevelOrderIso K m).symm E).2)).symm

end Galois

end TauCeti.puiseuxField
