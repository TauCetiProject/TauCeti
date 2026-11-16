/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.NormedField
public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.NumberTheory.LocalField.RamificationIndex
public import TauCeti.NumberTheory.Padics.LogGauge
public import TauCeti.RingTheory.Valuation.Discrete.Extension
public import TauCeti.RingTheory.Valuation.ValuativeRel.ValueGroup

/-!
# Discrete valuations of nonarchimedean local fields

For a nonarchimedean local field `K`, `𝒪[K]` is a discrete valuation ring, so
`ValuativeRel.isRankOneDiscrete_valuation` equips `ValuativeRel.valuation K` with a
`Valuation.IsRankOneDiscrete` instance. This file connects its normalized valuations
`intValuation`, `intAddVal`, `realAddVal`, and `extRealAddVal` with the local-field API
(`normalizedValuation`, `normalizedValuationWithZero`, `normalizedNormedField`,
`ramificationIndex`, `IsTotallyRamified`) and with Mathlib's concrete valuations on `ℚ_[p]`.

## Main results

* `TauCeti.normalizedValuationWithZero_eq_inv_intValuation`,
  `TauCeti.intAddVal_valuation_coe`, and `TauCeti.realAddVal_valuation_coe`: comparison of
  `intValuation`, `intAddVal`, and `realAddVal` on `K` with `normalizedValuationWithZero` and
  `normalizedValuation`.
* `TauCeti.normalizedNormedField_norm_eq_rpow_neg_realAddVal`: the norm of
  `normalizedNormedField K` satisfies `‖x‖ = (Nat.card 𝓀[K]) ^ (-((valuation K).realAddVal x))` for
  `x ≠ 0`.
* `TauCeti.ramificationIdx_valuation_eq_ramificationIndex`,
  `TauCeti.isTotallyRamified_iff_ramificationIdx_eq_finrank`, and
  `TauCeti.extRealAddVal_valuation_coe`: for any subfield `K` of a nonarchimedean local field `L`,
  `(valuation L).ramificationIdx K = ramificationIndex K L`, and `(valuation L).extRealAddVal K`
  agrees on `Lˣ` with `(normalizedValuation L x).toAdd / ramificationIndex K L`.
* `Padic.intValuation_valuation`, `Padic.intAddVal_valuation`, and
  `TauCeti.realAddVal_valuation_padic`: on `ℚ_[p]`, `(valuation ℚ_[p]).intValuation`,
  `intAddVal`, and `realAddVal` agree with `Padic.mulValuation`, `Padic.addValuation`, and
  `TauCeti.padicRealValuation p`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter I, §§1, 4 and Chapter II, §1.
-/

public section
noncomputable section

open ValuativeRel IsNonarchimedeanLocalField
open scoped WithZero NNRat

namespace TauCeti

section SingleField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- On a nonarchimedean local field `K`, `normalizedValuationWithZero K` is the pointwise inverse
of `(valuation K).intValuation`. -/
theorem normalizedValuationWithZero_eq_inv_intValuation (x : K) :
    normalizedValuationWithZero K x = ((valuation K).intValuation x)⁻¹ :=
  (valuation K).intValuation.normalizedValuationWithZero_eq_inv_of_surjective
    (valuation K).intValuation_surjective x

/-- On a nonarchimedean local field `K`, `(valuation K).intValuation` is the pointwise inverse of
`normalizedValuationWithZero K`. -/
theorem intValuation_valuation_apply (x : K) :
    (valuation K).intValuation x = (normalizedValuationWithZero K x)⁻¹ := by
  rw [normalizedValuationWithZero_eq_inv_intValuation, inv_inv]

/-- On `Kˣ`, the additive normalized valuation `(normalizedValuation K x).toAdd` agrees with
`Valuation.ord (valuation K).intValuation x`. -/
theorem toAdd_normalizedValuation_eq_ord_intValuation (x : Kˣ) :
    (normalizedValuation K x).toAdd = Valuation.ord (valuation K).intValuation (x : K) := by
  have h := normalizedValuationWithZero_eq_inv_intValuation (x : K)
  have hcoe : (normalizedValuation K x : ℤᵐ⁰) = WithZero.exp (normalizedValuation K x).toAdd := by
    rw [WithZero.exp_eq_coe_ofAdd, ofAdd_toAdd]
  rw [normalizedValuationWithZero_coe, hcoe,
    Valuation.valuation_eq_exp_neg_ord (valuation K).intValuation
      ((valuation K).intValuation.ne_zero_iff.mpr x.ne_zero),
    ← WithZero.exp_neg, neg_neg] at h
  exact WithZero.exp_injective h

/-- On `Kˣ`, `(valuation K).intAddVal` agrees with `(normalizedValuation K x).toAdd`. -/
@[simp]
theorem intAddVal_valuation_coe (x : Kˣ) :
    (valuation K).intAddVal (x : K) = ((normalizedValuation K x).toAdd : WithTop ℤ) := by
  rw [(valuation K).intAddVal_of_ne_zero x.ne_zero, toAdd_normalizedValuation_eq_ord_intValuation]

/-- On `Kˣ`, `(valuation K).realAddVal` agrees with `(normalizedValuation K x).toAdd` cast to
`ℝ`. -/
@[simp]
theorem realAddVal_valuation_coe (x : Kˣ) :
    (valuation K).realAddVal (x : K) = (((normalizedValuation K x).toAdd : ℝ) : WithTop ℝ) := by
  rw [(valuation K).realAddVal_eq_map, intAddVal_valuation_coe, WithTop.map_coe]

/-- Outside `0`, `((valuation K).realAddVal x).untop₀` is the additive normalized valuation of
`x`. -/
theorem untop₀_realAddVal_valuation_of_ne_zero {x : K} (hx : x ≠ 0) :
    ((valuation K).realAddVal x).untop₀ = (normalizedValuation K (Units.mk0 x hx)).toAdd := by
  simpa using congrArg WithTop.untop₀ (realAddVal_valuation_coe (Units.mk0 x hx))

/-- In `normalizedNormedField K`, every nonzero element has norm
`(Nat.card 𝓀[K]) ^ (-((valuation K).realAddVal x).untop₀)`. -/
theorem normalizedNormedField_norm_eq_rpow_neg_realAddVal {x : K} (hx : x ≠ 0) :
    letI := normalizedNormedField K
    ‖x‖ = (Nat.card 𝓀[K] : ℝ) ^ (-((valuation K).realAddVal x).untop₀) := by
  let _ := normalizedNormedField K
  rw [normalizedNormedField_norm_def, normalizedAbsoluteValue_apply_ne_zero x hx,
    untop₀_realAddVal_valuation_of_ne_zero hx, NNRat.cast_zpow, NNRat.cast_natCast,
    ← Real.rpow_intCast, Int.cast_neg]

end SingleField

section Extension

variable {K L : Type*} [Field K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L]

/-- For any subfield `K` of a nonarchimedean local field `L`, the value-group ramification index
`(valuation L).ramificationIdx K` equals `ramificationIndex K L`. -/
@[simp]
theorem ramificationIdx_valuation_eq_ramificationIndex :
    (valuation L).ramificationIdx K = ramificationIndex K L := by
  let e : ℤᵐ⁰ˣ ≃* Multiplicative ℤ :=
    WithZero.unitsWithZeroEquiv.trans (MulEquiv.inv (Multiplicative ℤ))
  have he_coe : ∀ γ : ℤᵐ⁰ˣ, (((e : ℤᵐ⁰ˣ →* Multiplicative ℤ) γ : Multiplicative ℤ) : ℤᵐ⁰) =
      (γ : ℤᵐ⁰)⁻¹ := fun γ ↦ by
    rw [MonoidHom.coe_ofClass, MulEquiv.trans_apply, MulEquiv.inv_apply, WithZero.coe_inv,
      WithZero.unitsWithZeroEquiv_apply, WithZero.coe_unzero]
  have htop : (valuation L).intValuation.valueGroup = ⊤ :=
    Valuation.valueGroup_eq_top_of_surjective _ (valuation L).intValuation_surjective
  have hmap :
      (((valuation L).intValuation.comap (algebraMap K L)).valueGroup).map
        (e : ℤᵐ⁰ˣ →* Multiplicative ℤ) =
        ((normalizedValuation L).comp (Units.map (algebraMap K L : K →* L))).range := by
    ext g
    rw [Subgroup.mem_map, MonoidHom.mem_range]
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      rw [← SetLike.mem_coe, ← MonoidWithZeroHom.valueMonoid_eq_valueGroup', SetLike.mem_coe,
        MonoidWithZeroHom.mem_valueMonoid_iff, Set.mem_preimage, Set.mem_range] at hγ
      obtain ⟨x, hx⟩ := hγ
      rw [Valuation.coe_toMonoidWithZeroHom, Valuation.comap_apply] at hx
      have hx0 : x ≠ 0 := fun h0 ↦ by
        rw [h0, map_zero, map_zero] at hx
        exact Units.ne_zero γ hx.symm
      refine ⟨Units.mk0 x hx0, WithZero.coe_inj.mp ?_⟩
      rw [MonoidHom.comp_apply, ← normalizedValuationWithZero_coe,
        Units.coe_map, MonoidHom.coe_ofClass, Units.val_mk0,
        normalizedValuationWithZero_eq_inv_intValuation, hx, he_coe]
    · rintro ⟨x, rfl⟩
      have hne : (valuation L).intValuation (algebraMap K L x) ≠ 0 :=
        (valuation L).intValuation.ne_zero_iff.mpr ((map_ne_zero (algebraMap K L)).mpr x.ne_zero)
      refine ⟨Units.mk0 _ hne, MonoidWithZeroHom.mem_valueGroup _ ⟨(x : K), ?_⟩,
        WithZero.coe_inj.mp ?_⟩
      · rw [Valuation.coe_toMonoidWithZeroHom, Valuation.comap_apply, Units.val_mk0]
      · rw [he_coe, Units.val_mk0, MonoidHom.comp_apply, ← normalizedValuationWithZero_coe,
          Units.coe_map, MonoidHom.coe_ofClass, normalizedValuationWithZero_eq_inv_intValuation]
  rw [(valuation L).isEquiv_intValuation.symm.ramificationIdx_eq, Valuation.ramificationIdx_def,
    htop, Subgroup.relIndex_top_right, ← Subgroup.index_map_equiv _ e, hmap,
    ramificationIndex_def]

/-- An extension `L / K` into a nonarchimedean local field `L` is totally ramified if and only if
`(valuation L).ramificationIdx K = Module.finrank K L`. -/
theorem isTotallyRamified_iff_ramificationIdx_eq_finrank :
    IsTotallyRamified K L ↔ (valuation L).ramificationIdx K = Module.finrank K L := by
  rw [isTotallyRamified_iff_ramificationIndex_eq_finrank,
    ramificationIdx_valuation_eq_ramificationIndex]

/-- On `Lˣ`, `(valuation L).extRealAddVal K` agrees with
`(normalizedValuation L x).toAdd / ramificationIndex K L`. -/
@[simp]
theorem extRealAddVal_valuation_coe (x : Lˣ) :
    (valuation L).extRealAddVal K (x : L) =
      ((((normalizedValuation L x).toAdd : ℝ) / (ramificationIndex K L : ℝ)) : WithTop ℝ) := by
  rw [(valuation L).extRealAddVal_eq_map_realAddVal, realAddVal_valuation_coe,
    WithTop.map_coe, ramificationIdx_valuation_eq_ramificationIndex]

/-- Outside `0`, `((valuation L).extRealAddVal K x).untop₀` is the additive normalized valuation of
`x` divided by `ramificationIndex K L`. -/
theorem untop₀_extRealAddVal_valuation_of_ne_zero {x : L} (hx : x ≠ 0) :
    ((valuation L).extRealAddVal K x).untop₀ =
      ((normalizedValuation L (Units.mk0 x hx)).toAdd : ℝ) / (ramificationIndex K L : ℝ) := by
  simpa using congrArg WithTop.untop₀ (extRealAddVal_valuation_coe (K := K) (Units.mk0 x hx))

end Extension

end TauCeti

section Padic

variable (p : ℕ) [Fact p.Prime]

namespace Padic

/-- On `ℚ_[p]`, the normalized `ℤᵐ⁰`-valued valuation of `ValuativeRel.valuation ℚ_[p]` is
`Padic.mulValuation`. -/
@[simp]
theorem intValuation_valuation :
    (ValuativeRel.valuation ℚ_[p]).intValuation = Padic.mulValuation := by
  ext x
  exact inv_injective <|
    (TauCeti.normalizedValuationWithZero_eq_inv_intValuation x).symm.trans
      (Padic.normalizedValuationWithZero_eq_inv_mulValuation p x)

/-- On `ℚ_[p]`, the normalized integer additive valuation of `ValuativeRel.valuation ℚ_[p]` is
`Padic.addValuation`. -/
@[simp]
theorem intAddVal_valuation :
    (ValuativeRel.valuation ℚ_[p]).intAddVal = Padic.addValuation := by
  ext x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simpa [Padic.addValuation.apply hx] using
      (TauCeti.intAddVal_valuation_coe (Units.mk0 x hx)).trans
        (congrArg ((↑) : ℤ → WithTop ℤ) (Padic.toAdd_normalizedValuation_eq_valuation p _))

end Padic

namespace TauCeti

/-- On `ℚ_[p]`, the normalized real additive valuation of `ValuativeRel.valuation ℚ_[p]` is
`TauCeti.padicRealValuation p`. -/
@[simp]
theorem realAddVal_valuation_padic :
    (valuation ℚ_[p]).realAddVal = padicRealValuation p := by
  ext x
  rw [Valuation.realAddVal_eq_map, Padic.intAddVal_valuation p, padicRealValuation_eq_map]

end TauCeti

end Padic
