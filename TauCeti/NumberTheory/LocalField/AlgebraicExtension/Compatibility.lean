/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.UnitsDecomposition
import Mathlib.RingTheory.Valuation.Algebraic
import TauCeti.NumberTheory.LocalField.PowerSubgroup.Basic

/-!
# Algebraic extensions of local fields are compatible with the valuations

Let `K` and `F` be nonarchimedean local fields, each with its own valuative relation, and let
`F` be an algebraic `K`-algebra. Nothing in this data asks the valuation of `F` to restrict to the
valuation of `K`; this file proves that it always does (`ValuativeExtension.of_isAlgebraic`). So
a hypothesis `ValuativeExtension K F` on such an algebra is automatic. For instance every finite
`ℚ_p`-algebra structure on a nonarchimedean local field is compatible with the `p`-adic valuation.

The argument is purely algebraic. Write `w` for the restriction to `K` of the valuation of `F`.

* A principal unit of `K` is an `n`-th power for every `n` prime to the residue characteristic,
  by Hensel's lemma (`TauCeti.unitFiltration_one_le_range_powMonoidHom_of_isUnit`). The value
  group of `F` is infinite cyclic, so `w` is trivial on principal units, and since the principal
  units have finite index in the units of `𝒪[K]`, it is trivial on all of them
  (`TauCeti.valuation_algebraMap_eq_one_of_mem_unitFiltration_zero`). This needs no algebraicity.
* Let `ϖ` be a uniformizer of `K`. If `w(ϖ) > 1`, then `w(1 - ϖ) = w(ϖ) > 1`, although `1 - ϖ` is
  a unit. If `w(ϖ) = 1`, then `w` is trivial on `K`, and so the valuation of `F`, a power of each
  of whose values is a value of `w` because `F/K` is algebraic, is trivial, which it is not. Hence
  `0 < w(ϖ) < 1`, and since every `x ∈ Kˣ` is `ϖ ^ k` times a unit, `w(x) < 1` exactly when `k > 0`,
  exactly when `v_K(x) < 1`.

## Main results

* `TauCeti.valuation_algebraMap_eq_one_of_mem_unitFiltration_zero`: a `K`-algebra structure on a
  nonarchimedean local field `F` sends the units of `𝒪[K]` to elements of valuation one.
* `ValuativeExtension.of_isAlgebraic`: an algebraic extension of nonarchimedean local fields is a
  valuative extension.

## References

* J.-P. Serre, *Local Fields*, Chapter II, §2, for the extension of the valuation to an algebraic
  extension.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, Proposition (5.3), for the structure of the
  unit group of a local field.
-/

public section

open ValuativeRel IsLocalRing

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra K F]

variable (F) in
/-- **The units of `𝒪[K]` keep valuation one in every local field over `K`.** For any
`K`-algebra structure on a nonarchimedean local field `F`, compatible with the valuations or not,
a unit `x` of the valuation ring of `K` has `v_F(x) = 1`. -/
theorem valuation_algebraMap_eq_one_of_mem_unitFiltration_zero {x : Kˣ}
    (hx : x ∈ unitFiltration K 0) : valuation F (algebraMap K F x) = 1 := by
  -- Read the valuation of `F` on `Kˣ` as an integer `k`.
  set φ : Kˣ →* Multiplicative ℤ :=
    (normalizedValuation F).comp (Units.map (algebraMap K F : K →* F))
  suffices hφ : φ x = 1 by
    simpa [φ, normalizedValuation_eq_one_iff] using hφ
  -- The `m`-th power of `x`, for `m = [U(K,0) : U(K,1)] ≠ 0`, is a principal unit.
  have hm : (unitFiltration K 1).relIndex (unitFiltration K 0) ≠ 0 := by
    rw [relIndex_unitFiltration_one_zero]
    exact Nat.sub_ne_zero_of_lt Finite.one_lt_card
  set m := (unitFiltration K 1).relIndex (unitFiltration K 0)
  have hxm : x ^ m ∈ unitFiltration K 1 := by
    have h := Subgroup.pow_index_mem ((unitFiltration K 1).subgroupOf (unitFiltration K 0))
      (⟨x, hx⟩ : unitFiltration K 0)
    rwa [Subgroup.mem_subgroupOf] at h
  -- Take `n` prime to the residue characteristic `c`, larger than `|m k|`.
  set k := (φ x).toAdd
  set c := ringChar 𝓀[K]
  have hc : c ≠ 0 := CharP.char_ne_zero_of_finite 𝓀[K] c
  set n := c * (m * k).natAbs + 1
  have hn : IsUnit (n : 𝒪[K]) := by
    rw [← residue_ne_zero_iff_isUnit, map_natCast]
    simp [n, c]
  -- Then `x ^ m = y ^ n` for some `y`, so `n ∣ m k`, which forces `m k = 0`.
  obtain ⟨y, hy⟩ := unitFiltration_one_le_range_powMonoidHom_of_isUnit hn hxm
  have hdvd : (n : ℤ) ∣ m * k := by
    refine ⟨(φ y).toAdd, ?_⟩
    have h := congrArg (fun z ↦ (φ z).toAdd) hy
    simpa [k, map_pow, toAdd_pow, mul_comm] using h.symm
  have hmk : m * k = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd <| by
    rw [Int.natAbs_natCast]
    exact Nat.lt_succ_of_le (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hc))
  rw [mul_eq_zero, Nat.cast_eq_zero] at hmk
  exact toAdd_eq_zero.mp (hmk.resolve_left hm)

/-- Write `x ∈ Kˣ` as `ϖ ^ k` times a unit, for the uniformizer `ϖ` given by an irreducible `π` of
`𝒪[K]`. Then the valuations of `x` in `K` and in `F` are the `k`-th powers of those of `ϖ`. -/
private theorem exists_valuation_eq_zpow_and_valuation_algebraMap_eq_zpow {π : 𝒪[K]}
    (hπ : Irreducible π) (x : Kˣ) :
    ∃ k : ℤ, valuation K (x : K) = valuation K (π : K) ^ k ∧
      valuation F (algebraMap K F x) = valuation F (algebraMap K F π) ^ k := by
  obtain ⟨⟨k, u⟩, rfl, -⟩ := existsUnique_eq_zpow_mul (normalizedValuation_irreducible hπ) x
  refine ⟨k, ?_, ?_⟩
  · rw [Units.val_mul, map_mul, (mem_unitFiltration_zero _).mp u.property, mul_one,
      Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_mk0]
  · rw [Units.val_mul, map_mul, map_mul,
      valuation_algebraMap_eq_one_of_mem_unitFiltration_zero F u.property, mul_one,
      Units.val_zpow_eq_zpow_val, map_zpow₀, map_zpow₀, Units.val_mk0]

/-- If `F` is algebraic over `K`, an irreducible element `π` of `𝒪[K]` has valuation less than
one in `F`. -/
private theorem valuation_algebraMap_lt_one_of_irreducible [Algebra.IsAlgebraic K F] {π : 𝒪[K]}
    (hπ : Irreducible π) : valuation F (algebraMap K F π) < 1 := by
  have hπ1 : valuation K (π : K) < 1 := Valuation.integer.v_irreducible_lt_one hπ
  refine lt_of_le_of_ne (not_lt.mp fun h ↦ ?_) fun h ↦ ?_
  · -- Otherwise the unit `1 - π` would have valuation `v_F(1 - π) = v_F(π) > 1` in `F`.
    have h1 : (1 - π : K) ≠ 0 := fun h0 ↦ hπ1.ne (by rw [← sub_eq_zero.mp h0, map_one])
    have hu : Units.mk0 _ h1 ∈ unitFiltration K 0 := by
      rw [mem_unitFiltration_zero, Units.val_mk0, (valuation K).map_one_sub_of_lt hπ1]
    have h2 := valuation_algebraMap_eq_one_of_mem_unitFiltration_zero F hu
    rw [Units.val_mk0, map_sub, map_one,
      Valuation.map_sub_eq_of_lt_right _ (by rwa [map_one])] at h2
    exact h.ne' h2
  · -- Otherwise the valuation of `F` would be trivial on `K`, hence on the algebraic `F/K`.
    obtain ⟨γ, hγ0, hγ1⟩ := IsNontrivial.exists_lt_one (R := F)
    obtain ⟨z, rfl⟩ := valuation_surjective γ
    obtain ⟨n, r, hn, -, hzr⟩ := (valuation F).exists_map_pow_eq_map_algebraMap_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic (R := K) z)
    have hr : r ≠ 0 := by
      rintro rfl
      rw [map_zero, map_zero, pow_eq_zero_iff hn.ne'] at hzr
      exact hγ0.ne' hzr
    obtain ⟨k, -, hk⟩ :=
      exists_valuation_eq_zpow_and_valuation_algebraMap_eq_zpow (F := F) hπ (Units.mk0 r hr)
    rw [h, one_zpow, Units.val_mk0] at hk
    exact (pow_lt_one₀ zero_le hγ1 hn.ne').ne (hzr.trans hk)

end TauCeti

open TauCeti

/-- **Algebraic extensions of local fields are valuative extensions.** If `F` is an algebraic
`K`-algebra, `K` and `F` nonarchimedean local fields, then the valuation of `F` restricts to the
valuation of `K`; no compatibility between the two valuative relations needs to be assumed. -/
theorem ValuativeExtension.of_isAlgebraic (K F : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra K F] [Algebra.IsAlgebraic K F] :
    ValuativeExtension K F := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hπ0 : (π : K) ≠ 0 := fun h ↦ hπ.ne_zero (Subtype.ext h)
  -- Both valuations of `x = π ^ k u` are `k`-th powers of values in `(0, 1)`, so both are `< 1`
  -- exactly when `k > 0`.
  have hequiv : ((valuation F).comap (algebraMap K F)).IsEquiv (valuation K) :=
    Valuation.isEquiv_iff_val_lt_one.mpr fun {x} ↦ by
      rcases eq_or_ne x 0 with rfl | hx
      · simp
      obtain ⟨k, hv, hw⟩ :=
        exists_valuation_eq_zpow_and_valuation_algebraMap_eq_zpow (F := F) hπ (Units.mk0 x hx)
      rw [Units.val_mk0] at hv hw
      rw [Valuation.comap_apply, hv, hw, zpow_lt_one_iff_right_of_lt_one₀
          (pos_iff_ne_zero.mpr (by simpa using hπ0))
          (valuation_algebraMap_lt_one_of_irreducible hπ),
        zpow_lt_one_iff_right_of_lt_one₀ (pos_iff_ne_zero.mpr (by simpa using hπ0))
          (Valuation.integer.v_irreducible_lt_one hπ)]
  exact ⟨fun {a b} ↦ by rw [(valuation F).vle_iff_le, (valuation K).vle_iff_le]; exact hequiv a b⟩
