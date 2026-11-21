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

For a nonarchimedean local field `K`, `ValuativeRel.isRankOneDiscrete_valuation` makes
`ValuativeRel.valuation K` rank-one discrete. This file relates its normalized valuations
`intValuation`, `intAddVal`, `realAddVal`, and `extRealAddVal` to the local-field API
(`normalizedValuation`, `normalizedValuationWithZero`, `normalizedNormedField`,
`ramificationIndex`, `IsTotallyRamified`) and Mathlib's concrete valuations on `ℚ_[p]`.

## Main results

* `TauCeti.normalizedValuationWithZero_eq_inv_intValuation`, `TauCeti.intAddVal_valuation_coe`,
  `TauCeti.realAddVal_valuation_coe`, and
  `TauCeti.normalizedNormedField_norm_eq_rpow_neg_realAddVal`: comparison with
  `normalizedValuationWithZero`, `normalizedValuation`, and `normalizedNormedField`.
* `TauCeti.ramificationIdx_valuation_eq_ramificationIndex`,
  `TauCeti.isTotallyRamified_iff_ramificationIdx_eq_finrank`, and
  `TauCeti.extRealAddVal_valuation_coe`: identification with `ramificationIndex K L` and
  `IsTotallyRamified K L` for any subfield `K` of a nonarchimedean local field `L`.
* `Padic.intValuation_valuation`, `Padic.intAddVal_valuation`, and
  `TauCeti.realAddVal_valuation_padic`: identification with `Padic.mulValuation`,
  `Padic.addValuation`, and `TauCeti.padicRealValuation p` on `ℚ_[p]`.

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

/-- On `Kˣ`, `(normalizedValuation K x).toAdd` equals `Valuation.ord (valuation K).intValuation x`.
-/
theorem toAdd_normalizedValuation_eq_ord_intValuation (x : Kˣ) :
    (normalizedValuation K x).toAdd = Valuation.ord (valuation K).intValuation (x : K) := by
  apply WithZero.exp_injective
  rw [WithZero.exp_eq_coe_ofAdd, ofAdd_toAdd, ← normalizedValuationWithZero_coe,
    normalizedValuationWithZero_eq_inv_intValuation,
    Valuation.valuation_eq_exp_neg_ord (valuation K).intValuation
      ((valuation K).intValuation.ne_zero_iff.mpr x.ne_zero),
    ← WithZero.exp_neg, neg_neg]

/-- On `Kˣ`, `(valuation K).intAddVal` agrees with `(normalizedValuation K x).toAdd`. -/
@[simp]
theorem intAddVal_valuation_coe (x : Kˣ) :
    (valuation K).intAddVal (x : K) = ((normalizedValuation K x).toAdd : WithTop ℤ) := by
  rw [(valuation K).intAddVal_of_ne_zero x.ne_zero, toAdd_normalizedValuation_eq_ord_intValuation]

/-- On `Kˣ`, `(valuation K).realAddVal` agrees with `(normalizedValuation K x).toAdd` in `ℝ`. -/
@[simp]
theorem realAddVal_valuation_coe (x : Kˣ) :
    (valuation K).realAddVal (x : K) = (((normalizedValuation K x).toAdd : ℝ) : WithTop ℝ) := by
  rw [(valuation K).realAddVal_eq_map, intAddVal_valuation_coe, WithTop.map_coe]

/-- Outside `0`, `((valuation K).realAddVal x).untop₀` is the additive normalized valuation. -/
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

private def intValuationUnitsEquiv : ℤᵐ⁰ˣ ≃* Multiplicative ℤ :=
  WithZero.unitsWithZeroEquiv.trans (MulEquiv.inv (Multiplicative ℤ))

private theorem intValuationUnitsEquiv_unitsMap (x : Kˣ) :
    intValuationUnitsEquiv (Units.map ((valuation K).intValuation : K →* ℤᵐ⁰) x) =
      normalizedValuation K x := by
  apply WithZero.coe_inj.mp
  rw [← normalizedValuationWithZero_coe, normalizedValuationWithZero_eq_inv_intValuation]
  simp [intValuationUnitsEquiv]

end SingleField

private theorem valueGroup_eq_range_unitsMap {A B : Type*} [GroupWithZero A] [GroupWithZero B]
    (f : A →*₀ B) : f.valueGroup = (Units.map f.toMonoidHom).range := by
  ext γ
  rw [← SetLike.mem_coe, ← MonoidWithZeroHom.valueMonoid_eq_valueGroup', SetLike.mem_coe,
    MonoidWithZeroHom.mem_valueMonoid_iff, MonoidHom.mem_range]
  refine ⟨fun ⟨a, ha⟩ ↦ ?_, fun ⟨a, ha⟩ ↦ ⟨a, congrArg Units.val ha⟩⟩
  have ha0 : a ≠ 0 := fun h0 ↦ Units.ne_zero γ (by simpa [h0] using ha.symm)
  exact ⟨Units.mk0 a ha0, Units.ext (by simpa using ha)⟩

section Extension

variable {K L : Type*} [Field K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L]

/-- For any subfield `K` of a nonarchimedean local field `L`, the value-group ramification index
`(valuation L).ramificationIdx K` equals `ramificationIndex K L`. -/
@[simp]
theorem ramificationIdx_valuation_eq_ramificationIndex :
    (valuation L).ramificationIdx K = ramificationIndex K L := by
  have htop : (valuation L).intValuation.valueGroup = ⊤ :=
    Valuation.valueGroup_eq_top_of_surjective _ (valuation L).intValuation_surjective
  have he_comp :
      (intValuationUnitsEquiv : ℤᵐ⁰ˣ →* Multiplicative ℤ).comp
          (Units.map ((valuation L).intValuation : L →* ℤᵐ⁰)) =
        normalizedValuation L :=
    MonoidHom.ext intValuationUnitsEquiv_unitsMap
  have hcomap :
      ((valuation L).intValuation.comap (algebraMap K L)).toMonoidWithZeroHom.toMonoidHom =
        ((valuation L).intValuation : L →* ℤᵐ⁰).comp (algebraMap K L : K →* L) :=
    MonoidHom.ext fun x ↦ (valuation L).intValuation.comap_apply (algebraMap K L) x
  have hmap : (((valuation L).intValuation.comap (algebraMap K L)).valueGroup).map
        (intValuationUnitsEquiv : ℤᵐ⁰ˣ →* Multiplicative ℤ) =
        ((normalizedValuation L).comp (Units.map (algebraMap K L : K →* L))).range := by
    rw [valueGroup_eq_range_unitsMap, hcomap, Units.map_comp, MonoidHom.map_range,
      ← MonoidHom.comp_assoc, he_comp]
  rw [(valuation L).isEquiv_intValuation.symm.ramificationIdx_eq, Valuation.ramificationIdx_def,
    htop, Subgroup.relIndex_top_right, ← Subgroup.index_map_equiv _ intValuationUnitsEquiv,
    hmap, ramificationIndex_def]

/-- `L / K` is totally ramified iff `(valuation L).ramificationIdx K = Module.finrank K L`. -/
theorem isTotallyRamified_iff_ramificationIdx_eq_finrank :
    IsTotallyRamified K L ↔ (valuation L).ramificationIdx K = Module.finrank K L := by
  rw [isTotallyRamified_iff_ramificationIndex_eq_finrank,
    ramificationIdx_valuation_eq_ramificationIndex]

/-- On `Lˣ`, `(valuation L).extRealAddVal K` is `(normalizedValuation L x).toAdd / e(L/K)`. -/
@[simp]
theorem extRealAddVal_valuation_coe (x : Lˣ) :
    (valuation L).extRealAddVal K (x : L) =
      ((((normalizedValuation L x).toAdd : ℝ) / (ramificationIndex K L : ℝ)) : WithTop ℝ) := by
  rw [(valuation L).extRealAddVal_eq_map_realAddVal, realAddVal_valuation_coe,
    WithTop.map_coe, ramificationIdx_valuation_eq_ramificationIndex]

/-- Outside `0`, `((valuation L).extRealAddVal K x).untop₀` is the normalized valuation over `e`. -/
theorem untop₀_extRealAddVal_valuation_of_ne_zero {x : L} (hx : x ≠ 0) :
    ((valuation L).extRealAddVal K x).untop₀ =
      ((normalizedValuation L (Units.mk0 x hx)).toAdd : ℝ) / (ramificationIndex K L : ℝ) := by
  simpa using congrArg WithTop.untop₀ (extRealAddVal_valuation_coe (K := K) (Units.mk0 x hx))

end Extension

end TauCeti

section Padic

variable (p : ℕ) [Fact p.Prime]

namespace Padic

/-- On `ℚ_[p]`, `(ValuativeRel.valuation ℚ_[p]).intValuation` equals `Padic.mulValuation`. -/
@[simp]
theorem intValuation_valuation :
    (ValuativeRel.valuation ℚ_[p]).intValuation = Padic.mulValuation := by
  ext x
  exact inv_injective <|
    (TauCeti.normalizedValuationWithZero_eq_inv_intValuation x).symm.trans
      (Padic.normalizedValuationWithZero_eq_inv_mulValuation p x)

/-- On `ℚ_[p]`, `(ValuativeRel.valuation ℚ_[p]).intAddVal` equals `Padic.addValuation`. -/
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

/-- On `ℚ_[p]`, `(valuation ℚ_[p]).realAddVal` equals `TauCeti.padicRealValuation p`. -/
@[simp]
theorem realAddVal_valuation_padic :
    (valuation ℚ_[p]).realAddVal = padicRealValuation p := by
  ext x
  rw [Valuation.realAddVal_eq_map, Padic.intAddVal_valuation p, padicRealValuation_eq_map]

end TauCeti

end Padic
