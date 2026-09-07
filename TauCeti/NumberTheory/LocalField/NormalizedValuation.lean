/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LocalField.Basic

/-!
# The normalized valuation of a nonarchimedean local field

Mathlib equips a nonarchimedean local field `K` with a valuation `ValuativeRel.valuation K`
taking values in an abstract value group `ValueGroupWithZero K`, together with an order
isomorphism `IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt` of that group with `ℤᵐ⁰`.
This file assembles them into the additively normalized valuation of a local field, the monoid
homomorphism

`normalizedValuation K : Kˣ →* Multiplicative ℤ`,

whose value at a uniformizer is `Multiplicative.ofAdd 1`. An integer is recovered from it by
decoding with `Multiplicative.toAdd`.

## Main definitions

* `TauCeti.normalizedValuation`: the normalized valuation `v_K^×` of a nonarchimedean local
  field, as a homomorphism from the unit group to `Multiplicative ℤ`.

## Main results

* `TauCeti.normalizedValuation_toAdd`: the translation between the multiplicative convention of
  `ValuativeRel.valuation` and the additive normalization.
* `TauCeti.normalizedValuation_surjective`: the normalized value group is all of `ℤ`.
* `TauCeti.normalizedValuation_irreducible`: an irreducible element of `𝒪[K]` has normalized
  valuation `1`; that is, uniformizers are exactly where the normalization is pinned.
* `TauCeti.eq_normalizedValuation`: the two previous properties characterize the normalized
  valuation among homomorphisms `Kˣ →* Multiplicative ℤ`.
* `TauCeti.normalizedValuation_eq_one_iff_isUnit`,
  `TauCeti.mem_integer_iff_toAdd_normalizedValuation_nonneg` and
  `TauCeti.dvd_iff_toAdd_normalizedValuation_le`: the normalized valuation reads off the units,
  the elements and the divisibility relation of the ring of integers.

## Implementation notes

Mathlib's convention is multiplicative and decreasing: `valuation K π < 1` at a uniformizer `π`,
and the integers of `K` are the elements of valuation at most `1`. The additive normalization
therefore carries a minus sign, and that sign is confined to the single translation lemma
`normalizedValuation_toAdd`; every statement mixing the two conventions is derived from it.

The normalized valuation is defined on `Kˣ` rather than on `K` because its target
`Multiplicative ℤ` is a group with no room for the value at `0`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter I, §§1–2.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §§3–4.
-/

public section
noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

open scoped WithZero

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

-- The declaration sequence follows the human-authored specification in
-- `TauCetiRoadmap/LocalFieldsRamification/Suggested.lean`.
variable (K) in
/-- The normalized valuation `v_K^×` of a nonarchimedean local field `K`: the composite of
`ValuativeRel.valuation K` with the order isomorphism `valueGroupWithZeroIsoInt` of the value
group with `ℤᵐ⁰`, read additively and with the sign chosen so that a uniformizer has value
`Multiplicative.ofAdd 1`. -/
def normalizedValuation : Kˣ →* Multiplicative ℤ :=
  invMonoidHom.comp
    ((((Units.mapEquiv (valueGroupWithZeroIsoInt K).toMulEquiv).trans
      WithZero.unitsWithZeroEquiv).toMonoidHom).comp
        (Units.map (valuation K).toMonoidWithZeroHom.toMonoidHom))

/-- The translation between Mathlib's multiplicative valuation and the additive normalization:
the normalized valuation is minus the logarithm of `ValuativeRel.valuation`, transported to
`ℤᵐ⁰`. Every comparison of the two conventions goes through this lemma. -/
theorem normalizedValuation_toAdd (x : Kˣ) :
    (normalizedValuation K x).toAdd
      = -WithZero.log (valueGroupWithZeroIsoInt K (valuation K (x : K))) := by
  simp [normalizedValuation, ← WithZero.toAdd_unzero_eq_log]

private theorem valueGroupWithZeroIsoInt_valuation_ne_zero (x : Kˣ) :
    valueGroupWithZeroIsoInt K (valuation K (x : K)) ≠ 0 := by
  simp

/-- The translation of `normalizedValuation_toAdd` read in the other direction: Mathlib's
valuation of a unit is recovered from the normalized valuation by exponentiating its negative. -/
theorem valueGroupWithZeroIsoInt_valuation (x : Kˣ) :
    valueGroupWithZeroIsoInt K (valuation K (x : K))
      = WithZero.exp (-(normalizedValuation K x).toAdd) := by
  rw [normalizedValuation_toAdd, neg_neg,
    WithZero.exp_log (valueGroupWithZeroIsoInt_valuation_ne_zero x)]

/-- The normalized valuation vanishes exactly on the elements of valuation `1`. -/
@[simp]
theorem normalizedValuation_eq_one_iff (x : Kˣ) :
    normalizedValuation K x = 1 ↔ valuation K (x : K) = 1 := by
  rw [← toAdd_eq_zero, normalizedValuation_toAdd, neg_eq_zero]
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have hx := WithZero.exp_log (valueGroupWithZeroIsoInt_valuation_ne_zero x)
  rw [h] at hx
  simpa using congrArg (valueGroupWithZeroIsoInt K).symm hx.symm

/-- The normalized valuation reverses the order of Mathlib's valuation. -/
theorem toAdd_normalizedValuation_le_iff_valuation_le (x y : Kˣ) :
    (normalizedValuation K x).toAdd ≤ (normalizedValuation K y).toAdd
      ↔ valuation K (y : K) ≤ valuation K (x : K) := by
  rw [normalizedValuation_toAdd, normalizedValuation_toAdd, neg_le_neg_iff,
    WithZero.log_le_log (valueGroupWithZeroIsoInt_valuation_ne_zero y)
      (valueGroupWithZeroIsoInt_valuation_ne_zero x),
    OrderIsoClass.map_le_map_iff]

/-- A unit of `K` lies in the ring of integers exactly when its normalized valuation is
nonnegative. -/
theorem mem_integer_iff_toAdd_normalizedValuation_nonneg (x : Kˣ) :
    (x : K) ∈ 𝒪[K] ↔ 0 ≤ (normalizedValuation K x).toAdd := by
  rw [normalizedValuation_toAdd, neg_nonneg,
    WithZero.log_le_iff_le_exp (valueGroupWithZeroIsoInt_valuation_ne_zero x), WithZero.exp_zero,
    ← map_one (valueGroupWithZeroIsoInt K), map_le_map_iff]
  exact Valuation.mem_integer_iff _ _

/-- The normalized value group of a nonarchimedean local field is all of `ℤ`. -/
theorem normalizedValuation_surjective : Function.Surjective (normalizedValuation K) := by
  intro n
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective
    ((valueGroupWithZeroIsoInt K).symm (WithZero.exp (-n.toAdd)))
  have hx0 : x ≠ 0 := by
    rw [← (valuation K).ne_zero_iff, hx]
    simp
  refine ⟨Units.mk0 x hx0, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [normalizedValuation_toAdd]
  simp [hx]

/-- An element of the ring of integers is a unit there exactly when its normalized valuation
vanishes. -/
theorem normalizedValuation_eq_one_iff_isUnit {u : 𝒪[K]} (hu : (u : K) ≠ 0) :
    normalizedValuation K (Units.mk0 (u : K) hu) = 1 ↔ IsUnit u := by
  rw [normalizedValuation_eq_one_iff, Units.val_mk0]
  exact (Valuation.Integers.isUnit_iff_valuation_eq_one
    (Valuation.integer.integers (valuation K))).symm

/-- Divisibility in the ring of integers is monotonicity of the normalized valuation. -/
theorem dvd_iff_toAdd_normalizedValuation_le {a b : 𝒪[K]} (ha : (a : K) ≠ 0) (hb : (b : K) ≠ 0) :
    a ∣ b ↔ (normalizedValuation K (Units.mk0 (a : K) ha)).toAdd
      ≤ (normalizedValuation K (Units.mk0 (b : K) hb)).toAdd := by
  rw [toAdd_normalizedValuation_le_iff_valuation_le]
  exact Valuation.Integers.dvd_iff_le (Valuation.integer.integers (valuation K))

/-- A root of unity has vanishing normalized valuation. -/
theorem normalizedValuation_eq_one_of_isOfFinOrder {x : Kˣ} (hx : IsOfFinOrder x) :
    normalizedValuation K x = 1 := by
  obtain ⟨n, hn, hxn⟩ := isOfFinOrder_iff_pow_eq_one.mp hx
  have hpow : normalizedValuation K x ^ n = 1 := by rw [← map_pow, hxn, map_one]
  rw [← toAdd_eq_zero] at hpow ⊢
  simpa [hn.ne'] using hpow

/-- Every unit of `K` is a unit of `𝒪[K]` times an integer power of a fixed irreducible element
of `𝒪[K]`. -/
theorem exists_eq_mul_zpow_of_irreducible {π : 𝒪[K]} (hπ : Irreducible π) (hπ0 : (π : K) ≠ 0)
    (x : Kˣ) :
    ∃ (u : Kˣ) (n : ℤ), valuation K (u : K) = 1 ∧ x = u * Units.mk0 (π : K) hπ0 ^ n := by
  have key : ∀ y : Kˣ, (y : K) ∈ 𝒪[K] →
      ∃ (u : Kˣ) (n : ℤ), valuation K (u : K) = 1 ∧ y = u * Units.mk0 (π : K) hπ0 ^ n := by
    intro y hy
    have hy0 : (⟨(y : K), hy⟩ : 𝒪[K]) ≠ 0 := by simp [Subtype.ext_iff]
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hπ
    have hu0 : ((u : 𝒪[K]) : K) ≠ 0 := by simp
    refine ⟨Units.mk0 ((u : 𝒪[K]) : K) hu0, n, ?_, ?_⟩
    · exact (Valuation.Integers.isUnit_iff_valuation_eq_one
        (Valuation.integer.integers (valuation K))).mp (u : 𝒪[K]ˣ).isUnit
    · apply Units.ext
      simpa using congrArg Subtype.val hu
  rcases le_total (valuation K (x : K)) 1 with h | h
  · exact key x h
  · have hmem : ((x⁻¹ : Kˣ) : K) ∈ 𝒪[K] := by
      rw [Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀]
      · exact h
      · exact zero_lt_iff.mpr ((valuation K).ne_zero_iff.mpr x.ne_zero)
    obtain ⟨u, n, hu, hx⟩ := key x⁻¹ hmem
    refine ⟨u⁻¹, -n, ?_, ?_⟩
    · simp [hu]
    · rw [← inv_inv x, hx]
      simp [mul_comm]

/-- The normalized valuation of an irreducible element of `𝒪[K]`, that is of a uniformizer of
`K`, is `Multiplicative.ofAdd 1`. -/
theorem normalizedValuation_irreducible {π : 𝒪[K]} (hπ : Irreducible π) (hπ0 : (π : K) ≠ 0) :
    normalizedValuation K (Units.mk0 (π : K) hπ0) = Multiplicative.ofAdd 1 := by
  have hlt : valuation K (π : K) < 1 := by
    refine lt_of_le_of_ne π.2 fun h => hπ.not_isUnit ?_
    exact (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (valuation K))).2 h
  have hpos : 0 < (normalizedValuation K (Units.mk0 (π : K) hπ0)).toAdd := by
    rw [normalizedValuation_toAdd, neg_pos,
      WithZero.log_lt_iff_lt_exp
        (valueGroupWithZeroIsoInt_valuation_ne_zero (Units.mk0 (π : K) hπ0)),
      WithZero.exp_zero, ← map_one (valueGroupWithZeroIsoInt K),
      map_lt_map_iff, Units.val_mk0]
    exact hlt
  obtain ⟨x, hx⟩ := normalizedValuation_surjective (K := K) (Multiplicative.ofAdd (1 : ℤ))
  obtain ⟨u, n, hu, rfl⟩ := exists_eq_mul_zpow_of_irreducible hπ hπ0 x
  rw [map_mul, (normalizedValuation_eq_one_iff u).2 hu, one_mul, map_zpow] at hx
  apply Multiplicative.toAdd.injective
  refine Int.eq_one_of_dvd_one hpos.le ⟨n, ?_⟩
  simpa [mul_comm] using congrArg Multiplicative.toAdd hx.symm

/-- The normalized valuation is the unique homomorphism `Kˣ →* Multiplicative ℤ` that vanishes
on the elements of valuation `1` and takes the value `Multiplicative.ofAdd 1` at a uniformizer. -/
theorem eq_normalizedValuation (w : Kˣ →* Multiplicative ℤ)
    (hw : ∀ x : Kˣ, valuation K (x : K) = 1 → w x = 1)
    {π : 𝒪[K]} (hπ : Irreducible π) (hπ0 : (π : K) ≠ 0)
    (hwπ : w (Units.mk0 (π : K) hπ0) = Multiplicative.ofAdd 1) :
    w = normalizedValuation K := by
  refine MonoidHom.ext fun x => ?_
  obtain ⟨u, n, hu, rfl⟩ := exists_eq_mul_zpow_of_irreducible hπ hπ0 x
  rw [map_mul, map_mul, hw u hu, (normalizedValuation_eq_one_iff u).2 hu, one_mul, one_mul,
    map_zpow, map_zpow, hwπ, normalizedValuation_irreducible hπ hπ0]

/-- The valuation of an irreducible element of `𝒪[K]` generates the value group: every nonzero
value is an integer power of it. -/
theorem exists_eq_valuation_zpow_of_irreducible {π : 𝒪[K]} (hπ : Irreducible π)
    (hπ0 : (π : K) ≠ 0) (γ : (ValueGroupWithZero K)ˣ) :
    ∃ n : ℤ, (γ : ValueGroupWithZero K) = valuation K (π : K) ^ n := by
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero K)
  have hy0 : y ≠ 0 := by
    rw [← (valuation K).ne_zero_iff, hy]
    exact γ.ne_zero
  have hπval : valueGroupWithZeroIsoInt K (valuation K (π : K)) = WithZero.exp (-1 : ℤ) := by
    have h := valueGroupWithZeroIsoInt_valuation (Units.mk0 (π : K) hπ0)
    rw [normalizedValuation_irreducible hπ hπ0] at h
    simpa using h
  have hzpow : ∀ (a : ValueGroupWithZero K) (m : ℤ),
      valueGroupWithZeroIsoInt K (a ^ m) = valueGroupWithZeroIsoInt K a ^ m :=
    fun a m => map_zpow₀ (valueGroupWithZeroIsoInt K).toMulEquiv a m
  refine ⟨(normalizedValuation K (Units.mk0 y hy0)).toAdd, ?_⟩
  apply EquivLike.injective (valueGroupWithZeroIsoInt K)
  rw [hzpow, hπval, ← hy]
  simpa using valueGroupWithZeroIsoInt_valuation (Units.mk0 y hy0)

end TauCeti
