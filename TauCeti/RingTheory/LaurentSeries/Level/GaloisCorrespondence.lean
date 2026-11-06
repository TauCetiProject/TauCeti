/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.Cyclic
public import TauCeti.RingTheory.LaurentSeries.Level.Kummer
public import TauCeti.RingTheory.LaurentSeries.RamificationIndex

/-!
# Fixed fields of the Kummer action on a ramified level

Let `K` be a field and `n ∣ m` positive integers. The level-`m` subfield `K⸨t ^ (1 / m)⸩` of the
Puiseux field contains the level-`n` subfield `K⸨t ^ (1 / n)⸩`, and the `m`-th roots of unity `η`
of `K` act on level `m` by the Kummer automorphisms `t ^ (1 / m) ↦ η t ^ (1 / m)`
(`TauCeti.puiseuxField.levelKummer`), which multiply the coefficient of `t ^ (k / m)` by `ηᵏ`.

The automorphism attached to `η` restricts on level `n` to the one attached to `η ^ (m / n)`, so it
fixes level `n` when `η ^ (m / n) = 1`. Conversely, if `η` is a primitive `(m / n)`-th root of
unity, a series of level `m` fixed by `η` has `ηᵏ = 1` at every exponent `k / m` of its support,
so `m / n` divides `k` and the exponent `k / m` has denominator dividing `n`. Thus the fixed field
of the Kummer automorphisms of the `(m / n)`-th roots of unity, the kernel of the power map
`η ↦ η ^ (m / n)`, is level `n`, as soon as `K` contains a primitive `(m / n)`-th root of unity.
This is computed on coefficients, without Galois theory.

When `K` contains a primitive `m`-th root of unity, level `m` is a cyclic Galois extension of
`K⸨X⸩` with group `μₘ(K)` (`TauCeti.puiseuxField.levelGalEquivRootsOfUnity`). The Galois
correspondence then identifies the subgroup fixing level `n` with the `(m / n)`-th roots of unity,
and since a cyclic group has exactly one subgroup of each index dividing its order, every
intermediate field of level `m` over `K⸨X⸩` is a level `n` with `n ∣ m`. Ordering the positive
integers by divisibility (`TauCeti.RamificationIndex`), this is an order isomorphism between the
divisors of `m` and the intermediate fields of level `m`.

## Main definitions

* `TauCeti.puiseuxField.restrictLevelOrderIso K m`: when `K` contains a primitive `m`-th root of
  unity, the order isomorphism `n ↦ level n` from the divisors of `m`, ordered by divisibility, to
  the intermediate fields of level `m` over `K⸨X⸩`.

## Main results

* `TauCeti.puiseuxField.levelKummer_apply_of_mem_ker`: the Kummer automorphism attached to an
  `(m / n)`-th root of unity fixes level `n`.
* `TauCeti.puiseuxField.levelKummer_apply_eq_self_iff`: for a primitive `(m / n)`-th root of unity
  `η`, a series of level `m` is fixed by `η` exactly when it lies in level `n`.
* `TauCeti.puiseuxField.fixedField_zpowers_levelKummer` and
  `TauCeti.puiseuxField.fixedField_map_ker_levelKummer`: the fixed field in level `m` of a primitive
  `(m / n)`-th root of unity, and of all `(m / n)`-th roots of unity, is level `n`.
* `TauCeti.puiseuxField.finrank_restrict_level`: level `n` has degree `n` over `K⸨X⸩` as an
  intermediate field of level `m`.
* `TauCeti.puiseuxField.fixingSubgroup_restrict_level` and
  `TauCeti.puiseuxField.mem_fixingSubgroup_restrict_level_iff`: with a primitive `m`-th root of
  unity in `K`, the automorphisms of level `m` fixing level `n` are the Kummer automorphisms of the
  `(m / n)`-th roots of unity.
* `TauCeti.puiseuxField.eq_restrict_level_of_finrank_eq`: with a primitive `m`-th root of unity in
  `K`, an intermediate field of level `m` of degree `n` is level `n`.
-/

public section

open IntermediateField Module
open scoped LaurentSeries

namespace TauCeti.puiseuxField

variable {K : Type*} [Field K] {n m : ℕ+}

/-- For `n ∣ m`, the Kummer automorphism of level `m` attached to an `m`-th root of unity `η` with
`η ^ (m / n) = 1` fixes every series of level `n`. -/
theorem levelKummer_apply_of_mem_ker (h : n ∣ m) {η : rootsOfUnity m K}
    (hη : η ∈ (rootsOfUnityPowOfDvd (M := K) (PNat.dvd_iff.mp h)).ker) {x : level K m}
    (hx : (x : puiseuxField K) ∈ level K n) : levelKummer K m η x = x := by
  have hx' : inclusion (level_le_level_of_dvd K h) ⟨x, hx⟩ = x := Subtype.ext (coe_inclusion _ _)
  rw [← hx', levelKummer_inclusion h, MonoidHom.mem_ker.mp hη, map_one, AlgEquiv.one_apply]

/-- For `n ∣ m` and a primitive `(m / n)`-th root of unity `η`, a series of level `m` is fixed by
the Kummer automorphism attached to `η` exactly when it lies in level `n`: at every exponent
`k / m` of the support of a fixed series, `ηᵏ = 1`, so `m / n` divides `k`. -/
theorem levelKummer_apply_eq_self_iff (h : n ∣ m) {η : rootsOfUnity m K}
    (hη : IsPrimitiveRoot ((η : Kˣ) : K) ((m : ℕ) / n)) (x : level K m) :
    levelKummer K m η x = x ↔ (x : puiseuxField K) ∈ level K n := by
  refine ⟨fun hx ↦ ?_,
    levelKummer_apply_of_mem_ker h (mem_ker_rootsOfUnityPowOfDvd_of_isPrimitiveRoot _ hη)⟩
  obtain ⟨e, rfl⟩ := h
  have he : ((n * e : ℕ+) : ℕ) / n = e := by rw [PNat.mul_coe, Nat.mul_div_cancel_left _ n.pos]
  rw [he] at hη
  have hxm := x.2
  rw [mem_level_iff, mem_range_levelEmbedding_iff, LaurentSeries.mem_range_ramifiedEmbedding_iff]
    at hxm ⊢
  intro q hq
  obtain ⟨k, rfl⟩ := (Rat.den_dvd_iff_exists_eq_intCast_div (n * e).ne_zero).mp (hxm q hq)
  -- Comparing the coefficients of `t ^ (k / (n * e))` gives `ηᵏ = 1`, hence `k = e * j`.
  have hcoeff := congrArg
    (fun y : level K (n * e) ↦ ((y : puiseuxField K) : HahnSeries ℚ K).coeff ((k : ℚ) / ↑(n * e)))
    hx
  simp only [coeff_levelKummer] at hcoeff
  obtain ⟨j, rfl⟩ := (hη.zpow_eq_one_iff_dvd k).mp
    ((mul_eq_right₀ ((HahnSeries.mem_support _ _).mp hq)).mp hcoeff)
  refine (Rat.den_dvd_iff_exists_eq_intCast_div n.ne_zero).mpr ⟨j, ?_⟩
  have he0 : (e : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr e.ne_zero
  push_cast
  field_simp

/-- **Fixed field of a primitive root of unity.** For `n ∣ m` and a primitive `(m / n)`-th root of
unity `η`, the series of level `m` fixed by the Kummer automorphism attached to `η` form level
`n`. -/
theorem fixedField_zpowers_levelKummer (h : n ∣ m) {η : rootsOfUnity m K}
    (hη : IsPrimitiveRoot ((η : Kˣ) : K) ((m : ℕ) / n)) :
    fixedField (Subgroup.zpowers (levelKummer K m η)) = restrict (level_le_level_of_dvd K h) := by
  ext x
  rw [mem_fixedField_iff, mem_restrict]
  refine ⟨fun hx ↦ (levelKummer_apply_eq_self_iff h hη x).mp (hx _ (Subgroup.mem_zpowers _)),
    fun hx ↦ ?_⟩
  -- The powers of the automorphism attached to `η` are attached to the powers of `η`, which are
  -- again `(m / n)`-th roots of unity.
  rintro _ ⟨k, rfl⟩
  simp only [← map_zpow]
  exact levelKummer_apply_of_mem_ker h
    (Subgroup.zpow_mem _ (mem_ker_rootsOfUnityPowOfDvd_of_isPrimitiveRoot _ hη) k) hx

/-- **Fixed field of the `(m / n)`-th roots of unity.** For `n ∣ m`, if `K` contains a primitive
`(m / n)`-th root of unity, then the series of level `m` fixed by the Kummer automorphisms of all
`(m / n)`-th roots of unity, the kernel of the power map `η ↦ η ^ (m / n)` from `μₘ(K)` to
`μₙ(K)`, form level `n`. -/
theorem fixedField_map_ker_levelKummer (h : n ∣ m) [HasEnoughRootsOfUnity K ((m : ℕ) / n)] :
    fixedField ((rootsOfUnityPowOfDvd (M := K) (PNat.dvd_iff.mp h)).ker.map (levelKummer K m)) =
      restrict (level_le_level_of_dvd K h) := by
  have : NeZero ((m : ℕ) / n) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd m.pos (PNat.dvd_iff.mp h)) n.pos).ne'⟩
  obtain ⟨η, hη⟩ := exists_rootsOfUnity_isPrimitiveRoot_of_dvd (M := K)
    (Nat.div_dvd_of_dvd (PNat.dvd_iff.mp h))
  refine le_antisymm ?_ fun x hx ↦ ?_
  · rw [← fixedField_zpowers_levelKummer h hη]
    exact fixedField_le
      (Subgroup.zpowers_le.mpr ⟨η, mem_ker_rootsOfUnityPowOfDvd_of_isPrimitiveRoot _ hη, rfl⟩)
  · rw [mem_fixedField_iff]
    rintro _ ⟨η', hη', rfl⟩
    exact levelKummer_apply_of_mem_ker h hη' ((mem_restrict _ x).mp hx)

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

/-- **Intermediate fields of a level.** For `n ∣ m`, if `K` contains a primitive `m`-th root of
unity, then the only intermediate field of level `m` over `K⸨X⸩` of degree `n` is level `n`. -/
theorem eq_restrict_level_of_finrank_eq (h : n ∣ m) {E : IntermediateField K⸨X⸩ (level K m)}
    (hE : finrank K⸨X⸩ E = n) : E = restrict (level_le_level_of_dvd K h) := by
  have : FiniteDimensional K⸨X⸩ (level K m) := (levelPowerBasis K m).finite
  have : IsCyclic Gal(level K m/K⸨X⸩) :=
    (levelGalEquivRootsOfUnity K m).isCyclic.mpr inferInstance
  exact eq_of_finrank_eq_of_isCyclic (by rw [hE, finrank_restrict_level h])

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
