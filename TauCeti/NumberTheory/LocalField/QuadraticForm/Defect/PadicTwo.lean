/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.LocalField
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Defect.Basic
public import TauCeti.NumberTheory.Padics.SerreSigns
import TauCeti.NumberTheory.LocalField.Padic
import TauCeti.NumberTheory.LocalField.QuadraticForm.Ramification.Dictionary

/-!
# The quadratic defect over `ℚ₂`

Over `ℚ₂` the normalized valuation of `2` is `1`, so O'Meara's list of the defects of units
(`TauCeti.quadraticDefect_eq_maximalIdeal_zpow_or_odd`) has the three entries `0`, `4 ℤ₂` and
`2 ℤ₂`. For a unit `u` of `ℤ₂`, which entry is `𝔡(u)` is read off `u mod 8`, through Serre's sign
functions `ε(u) = (u − 1)/2` and `ω(u) = (u² − 1)/8` modulo `2`:

* `𝔡(u) = 0` if `u ≡ 1 mod 8`, that is `ε(u) = ω(u) = 0`;
* `𝔡(u) = 4 ℤ₂` if `u ≡ 5 mod 8`, that is `ε(u) = 0` and `ω(u) = 1`;
* `𝔡(u) = 2 ℤ₂` if `u ≡ 3 mod 4`, that is `ε(u) = 1`.

Thus `𝔡(1) = 0`, as for every square, while `5` attains the maximal finite defect `4 ℤ₂` and `-1`
the odd defect `2 ℤ₂`. The value `𝔡(-5) = 2 ℤ₂` shows that the defect is not multiplicative:
`𝔡(-1) 𝔡(5) = 8 ℤ₂ ≠ 𝔡(-5)`.

## Main results

* `TauCeti.quadraticDefect_eq_zero_iff_padicTwo`: `𝔡(u) = 0` if and only if `ε(u) = ω(u) = 0`.
* `TauCeti.defectExponent_of_serreOmega_eq_one_padicTwo`,
  `TauCeti.quadraticDefect_of_serreOmega_eq_one_padicTwo`: if `ε(u) = 0` and `ω(u) = 1`, then
  `δ(u) = 2` and `𝔡(u) = 4 ℤ₂`.
* `TauCeti.defectExponent_of_serreEps_eq_one_padicTwo`,
  `TauCeti.quadraticDefect_of_serreEps_eq_one_padicTwo`: if `ε(u) = 1`, then `δ(u) = 1` and
  `𝔡(u) = 2 ℤ₂`.
* `TauCeti.quadraticDefect_five_padicTwo`, `TauCeti.quadraticDefect_neg_one_padicTwo`,
  `TauCeti.quadraticDefect_neg_five_padicTwo`: `𝔡(5) = 4 ℤ₂`, `𝔡(-1) = 2 ℤ₂` and
  `𝔡(-5) = 2 ℤ₂`.
* `TauCeti.quadraticDefect_neg_one_mul_five_ne_padicTwo`: `𝔡(-1 · 5) ≠ 𝔡(-1) 𝔡(5)`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A, in particular 63:2.
* J.-P. Serre, *A Course in Arithmetic*, Chapter II, §3.3.
-/

public section

noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

/-- A unit of `ℤ₂` has normalized valuation zero in `ℚ₂`. -/
private theorem toAdd_normalizedValuation_eq_zero_of_coe_eq {a : ℚ_[2]ˣ} {u : ℤ_[2]ˣ}
    (ha : (a : ℚ_[2]) = u) : (normalizedValuation ℚ_[2] a).toAdd = 0 := by
  rw [Padic.toAdd_normalizedValuation_eq_valuation, ha, PadicInt.valuation_coe,
    PadicInt.valuation_eq_zero_of_isUnit u.isUnit, Nat.cast_zero]

/-- A unit of `ℤ₂` has valuation one in `ℚ₂`. -/
private theorem valuation_eq_one_of_coe_eq {a : ℚ_[2]ˣ} {u : ℤ_[2]ˣ} (ha : (a : ℚ_[2]) = u) :
    valuation ℚ_[2] (a : ℚ_[2]) = 1 :=
  (normalizedValuation_eq_one_iff a).mp
    (toAdd_eq_zero.mp (toAdd_normalizedValuation_eq_zero_of_coe_eq ha))

/-- A unit `u` of `ℤ₂` is a square in `ℚ₂` exactly when `ε(u) = ω(u) = 0`. -/
private theorem isSquare_iff_of_coe_eq {a : ℚ_[2]ˣ} {u : ℤ_[2]ˣ} (ha : (a : ℚ_[2]) = u) :
    IsSquare a ↔ serreEps u = 0 ∧ serreOmega u = 0 := by
  rw [← isSquare_units_val_iff, ha, isSquare_coe_iff_mem_unitsPrincipal_three,
    serreEps_eq_zero_and_serreOmega_eq_zero_iff]

/-- `5` as a unit of `ℤ₂`. -/
private def padicIntUnitFive : ℤ_[2]ˣ := isUnit_five_padicInt.unit

private theorem val_padicIntUnitFive : ((padicIntUnitFive : ℤ_[2]ˣ) : ℤ_[2]) = 5 :=
  IsUnit.unit_spec _

private theorem coe_padicIntUnitFive :
    (((padicIntUnitFive : ℤ_[2]ˣ) : ℤ_[2]) : ℚ_[2]) = 5 := by
  rw [val_padicIntUnitFive]
  norm_cast

/-- The principal fractional ideal of `2 ^ n` is `𝓂[ℚ₂] ^ n`. -/
private theorem spanSingleton_two_pow_eq_maximalIdeal_zpow (n : ℕ) :
    FractionalIdeal.spanSingleton (nonZeroDivisors 𝒪[ℚ_[2]]) ((2 : ℚ_[2]) ^ n) =
      ((IsLocalRing.maximalIdeal 𝒪[ℚ_[2]] : Ideal 𝒪[ℚ_[2]]) :
        FractionalIdeal (nonZeroDivisors 𝒪[ℚ_[2]]) ℚ_[2]) ^ (n : ℤ) := by
  have h := Units.spanSingleton_eq_maximalIdeal_zpow (Units.mk0 ((2 : ℚ_[2]) ^ n) (by simp))
  rw [Padic.toAdd_normalizedValuation_eq_valuation, Units.val_mk0, Padic.valuation_pow] at h
  simpa using h

/-- `δ(5) = 2` over `ℚ₂`: the approximation `5 − 1² = 4` attains the upper bound `2 v(2)` of
the defect exponent of a nonsquare unit. -/
private theorem defectExponent_five :
    defectExponent (Units.mk0 (5 : ℚ_[2]) (by norm_num)) = 2 := by
  have hsq : ¬IsSquare (Units.mk0 (5 : ℚ_[2]) (by norm_num)) :=
    fun h => Padic.not_isSquare_five (isSquare_units_val_iff.mpr h)
  have hval : valuation ℚ_[2] ((Units.mk0 (5 : ℚ_[2]) (by norm_num) : ℚ_[2]ˣ) : ℚ_[2]) = 1 :=
    valuation_eq_one_of_coe_eq (u := padicIntUnitFive) coe_padicIntUnitFive.symm
  refine le_antisymm ?_ ?_
  · simpa [Padic.natCastValuation_self 2] using
      defectExponent_le_two_mul_natCastValuation two_ne_zero hval hsq
  · have h := le_defectExponent (Units.mk0 (5 : ℚ_[2]) (by norm_num)) 1
      (Units.mk0 ((2 : ℚ_[2]) ^ 2) (by simp)) (by norm_num)
    rw [Padic.toAdd_normalizedValuation_eq_valuation, Units.val_mk0, Padic.valuation_pow] at h
    simpa using h

/-- **The units of maximal defect over `ℚ₂`.** If `u ∈ ℤ₂ˣ` is `5 mod 8`, that is `ε(u) = 0`
and `ω(u) = 1`, then its defect exponent is `2 = 2 v(2)`. -/
theorem defectExponent_of_serreOmega_eq_one_padicTwo {a : ℚ_[2]ˣ} {u : ℤ_[2]ˣ}
    (ha : (a : ℚ_[2]) = u) (hε : serreEps u = 0) (hω : serreOmega u = 1) :
    defectExponent a = 2 := by
  -- Up to the square of a unit `w`, `u` is `5`.
  obtain ⟨w, hw⟩ := exists_eq_neg_one_pow_mul_five_pow_mul_sq u
  have hfive : a = Units.mk0 (5 : ℚ_[2]) (by norm_num) *
      Units.map PadicInt.Coe.ringHom.toMonoidHom w ^ 2 := by
    ext
    rw [ha, hw, hε, hω]
    simp [ZMod.val_one]
    norm_cast
  rw [hfive, defectExponent_mul_sq, defectExponent_five,
    toAdd_normalizedValuation_eq_zero_of_coe_eq (u := w) rfl]
  norm_num

/-- **The units of odd defect over `ℚ₂`.** If `u ∈ ℤ₂ˣ` is `3 mod 4`, that is `ε(u) = 1`, then
its defect exponent is `1`. -/
theorem defectExponent_of_serreEps_eq_one_padicTwo {a : ℚ_[2]ˣ} {u : ℤ_[2]ˣ}
    (ha : (a : ℚ_[2]) = u) (hε : serreEps u = 1) :
    defectExponent a = 1 := by
  have hval := valuation_eq_one_of_coe_eq ha
  have hsq : ¬IsSquare a := by
    rw [isSquare_iff_of_coe_eq ha, hε]
    simp
  rcases defectExponent_eq_two_mul_natCastValuation_or_odd two_ne_zero hval hsq with h | ⟨k, hk, h⟩
  · -- Two units of maximal defect differ by a square, but `ε(5 u) = 1` says `5 u` is not one.
    have h5 : defectExponent (Units.mk0 (5 : ℚ_[2]) (by norm_num)) =
        ((2 * natCastValuation ℚ_[2] 2 two_ne_zero : ℕ) : ℤ) := by
      rw [defectExponent_five, Padic.natCastValuation_self 2]
      norm_num
    have hprod := isSquare_mul_of_defectExponent_eq_two_mul two_ne_zero hval
      (valuation_eq_one_of_coe_eq (u := padicIntUnitFive) coe_padicIntUnitFive.symm) h h5
    have hcoe : ((a * Units.mk0 (5 : ℚ_[2]) (by norm_num) : ℚ_[2]ˣ) : ℚ_[2]) =
        ((u * padicIntUnitFive : ℤ_[2]ˣ) : ℤ_[2]) := by
      simp [ha, coe_padicIntUnitFive]
    rw [isSquare_iff_of_coe_eq hcoe, serreEps_mul, hε,
      serreEps_eq_zero_of_coe_eq_five val_padicIntUnitFive] at hprod
    simp at hprod
  · rw [Padic.natCastValuation_self 2] at hk
    obtain rfl : k = 0 := by omega
    exact h

/-- **The square units of `ℤ₂` have defect zero.** A unit `u` of `ℤ₂` has quadratic defect `0`
in `ℚ₂` if and only if `u ≡ 1 mod 8`, that is `ε(u) = ω(u) = 0`. -/
theorem quadraticDefect_eq_zero_iff_padicTwo {a : ℚ_[2]ˣ} {u : ℤ_[2]ˣ}
    (ha : (a : ℚ_[2]) = u) :
    quadraticDefect a = 0 ↔ serreEps u = 0 ∧ serreOmega u = 0 := by
  rw [quadraticDefect_eq_zero_iff, isSquare_iff_of_coe_eq ha]

/-- **The units of maximal defect over `ℚ₂`, as ideals.** If `u ∈ ℤ₂ˣ` is `5 mod 8`, that is
`ε(u) = 0` and `ω(u) = 1`, then `𝔡(u) = 4 ℤ₂`. -/
theorem quadraticDefect_of_serreOmega_eq_one_padicTwo {a : ℚ_[2]ˣ} {u : ℤ_[2]ˣ}
    (ha : (a : ℚ_[2]) = u) (hε : serreEps u = 0) (hω : serreOmega u = 1) :
    quadraticDefect a = FractionalIdeal.spanSingleton _ 4 := by
  rw [quadraticDefect_eq_maximalIdeal_zpow (defectExponent_of_serreOmega_eq_one_padicTwo ha hε hω),
    show (4 : ℚ_[2]) = 2 ^ 2 by norm_num, spanSingleton_two_pow_eq_maximalIdeal_zpow]

/-- **The units of odd defect over `ℚ₂`, as ideals.** If `u ∈ ℤ₂ˣ` is `3 mod 4`, that is
`ε(u) = 1`, then `𝔡(u) = 2 ℤ₂`. -/
theorem quadraticDefect_of_serreEps_eq_one_padicTwo {a : ℚ_[2]ˣ} {u : ℤ_[2]ˣ}
    (ha : (a : ℚ_[2]) = u) (hε : serreEps u = 1) :
    quadraticDefect a = FractionalIdeal.spanSingleton _ 2 := by
  rw [quadraticDefect_eq_maximalIdeal_zpow (defectExponent_of_serreEps_eq_one_padicTwo ha hε),
    ← pow_one (2 : ℚ_[2]), spanSingleton_two_pow_eq_maximalIdeal_zpow, Nat.cast_one]

/-- `𝔡(5) = 4 ℤ₂` over `ℚ₂`. -/
theorem quadraticDefect_five_padicTwo :
    quadraticDefect (Units.mk0 (5 : ℚ_[2]) (by norm_num)) = FractionalIdeal.spanSingleton _ 4 :=
  quadraticDefect_of_serreOmega_eq_one_padicTwo (u := padicIntUnitFive) coe_padicIntUnitFive.symm
    (serreEps_eq_zero_of_coe_eq_five val_padicIntUnitFive)
    (serreOmega_eq_one_of_coe_eq_five val_padicIntUnitFive)

/-- `𝔡(-1) = 2 ℤ₂` over `ℚ₂`. -/
theorem quadraticDefect_neg_one_padicTwo :
    quadraticDefect (-1 : ℚ_[2]ˣ) = FractionalIdeal.spanSingleton _ 2 :=
  quadraticDefect_of_serreEps_eq_one_padicTwo (u := -1) (by simp) serreEps_neg_one

/-- `𝔡(-5) = 2 ℤ₂` over `ℚ₂`, since `-5 ≡ 3 mod 4`. -/
theorem quadraticDefect_neg_five_padicTwo :
    quadraticDefect (-Units.mk0 (5 : ℚ_[2]) (by norm_num)) = FractionalIdeal.spanSingleton _ 2 :=
  quadraticDefect_of_serreEps_eq_one_padicTwo (u := -padicIntUnitFive)
    (by simp [coe_padicIntUnitFive]) (by
      rw [neg_eq_neg_one_mul, serreEps_mul, serreEps_neg_one,
        serreEps_eq_zero_of_coe_eq_five val_padicIntUnitFive, add_zero])

/-- **The quadratic defect is not multiplicative.** Over `ℚ₂`, `𝔡(-1) = 2 ℤ₂` and `𝔡(5) = 4 ℤ₂`,
but `𝔡(-1 · 5) = 𝔡(-5) = 2 ℤ₂` is not `8 ℤ₂`. -/
theorem quadraticDefect_neg_one_mul_five_ne_padicTwo :
    quadraticDefect (-1 * Units.mk0 (5 : ℚ_[2]) (by norm_num)) ≠
      quadraticDefect (-1) * quadraticDefect (Units.mk0 (5 : ℚ_[2]) (by norm_num)) := by
  rw [neg_one_mul, quadraticDefect_neg_five_padicTwo, quadraticDefect_neg_one_padicTwo,
    quadraticDefect_five_padicTwo, ← map_mul]
  intro h
  -- Comparing valuations, `2 ℤ₂ ⊆ 8 ℤ₂` would give `v(8) ≤ v(2)`, that is `3 ≤ 1`.
  have hle := (toAdd_normalizedValuation_le_iff_valuation_le
    (Units.mk0 ((2 : ℚ_[2]) ^ 3) (by simp)) (Units.mk0 ((2 : ℚ_[2]) ^ 1) (by simp))).mpr
      (by simpa [show (2 : ℚ_[2]) * 4 = 2 ^ 3 by norm_num] using
        spanSingleton_le_spanSingleton_iff_valuation_le.mp h.le)
  rw [Padic.toAdd_normalizedValuation_eq_valuation, Padic.toAdd_normalizedValuation_eq_valuation,
    Units.val_mk0, Units.val_mk0, Padic.valuation_pow, Padic.valuation_pow] at hle
  simp at hle

end TauCeti
