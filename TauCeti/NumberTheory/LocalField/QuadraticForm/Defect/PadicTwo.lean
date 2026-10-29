/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.LocalField
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Defect.Basic
public import TauCeti.NumberTheory.LocalField.QuadraticForm.PadicTwo
public import TauCeti.NumberTheory.Padics.SerreSigns
import TauCeti.NumberTheory.LocalField.Padic
import TauCeti.NumberTheory.LocalField.QuadraticForm.Ramification.Dictionary
import TauCeti.NumberTheory.Padics.PadicIntegers

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

More generally, write `a ∈ ℚ₂ˣ` as `a = 2 ^ α u` with `u` a unit of `ℤ₂`. The defect exponent
`δ(a) = sup_ξ v(a - ξ²)` is

* `α` when `α` is odd;
* `α + 1` when `α` is even and `u ≡ 3 mod 4`, that is `ε(u) = 1`;
* `α + 2` when `α` is even and `u ≡ 5 mod 8`;
* `⊤` when `α` is even and `u ≡ 1 mod 8`, that is when `a` is a square.

On the eight representatives `1, -1, 5, -5, 2, -2, 10, -10` of the square classes of `ℚ₂`
(`TauCeti.padicTwoSquareClassRep`) the defects are `0, 2, 4, 2, 2, 2, 2, 2` times `ℤ₂`.

## Main results

* `TauCeti.quadraticDefect_eq_zero_iff_padicTwo`: `𝔡(u) = 0` if and only if `ε(u) = ω(u) = 0`.
* `TauCeti.defectExponent_of_serreEps_eq_zero_of_serreOmega_eq_one_padicTwo`,
  `TauCeti.quadraticDefect_of_serreEps_eq_zero_of_serreOmega_eq_one_padicTwo`: if `ε(u) = 0`
  and `ω(u) = 1`, then `δ(u) = 2` and `𝔡(u) = 4 ℤ₂`.
* `TauCeti.defectExponent_of_serreEps_eq_one_padicTwo`,
  `TauCeti.quadraticDefect_of_serreEps_eq_one_padicTwo`: if `ε(u) = 1`, then `δ(u) = 1` and
  `𝔡(u) = 2 ℤ₂`.
* `TauCeti.defectExponent_padicTwo`: the defect exponent of `2 ^ α u` over `ℚ₂`.
* `TauCeti.quadraticDefect_five_padicTwo`, `TauCeti.quadraticDefect_neg_one_padicTwo`,
  `TauCeti.quadraticDefect_neg_five_padicTwo`: `𝔡(5) = 4 ℤ₂`, `𝔡(-1) = 2 ℤ₂` and
  `𝔡(-5) = 2 ℤ₂`.
* `TauCeti.defectExponent_padicTwoSquareClassRep` and
  `TauCeti.quadraticDefect_padicTwoSquareClassRep`: the defect exponents and the defects of the
  eight square-class representatives.
* `TauCeti.quadraticDefect_neg_one_mul_five_ne_mul_padicTwo`: `𝔡(-1 · 5) ≠ 𝔡(-1) 𝔡(5)`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A, 63:2 and 63:3.
* J.-P. Serre, *A Course in Arithmetic*, Chapter II, §3.3.
-/

public section

noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

/-- `5` as a unit of `ℤ₂`. -/
private def padicIntUnitFive : ℤ_[2]ˣ := isUnit_five_padicInt.unit

private theorem val_padicIntUnitFive : ((padicIntUnitFive : ℤ_[2]ˣ) : ℤ_[2]) = 5 :=
  IsUnit.unit_spec _

private theorem coe_padicIntUnitFive :
    (((padicIntUnitFive : ℤ_[2]ˣ) : ℤ_[2]) : ℚ_[2]) = 5 := by
  rw [val_padicIntUnitFive]
  norm_cast

/-- `ε(-5) = 1`, since `-5 ≡ 3 mod 4`. -/
private theorem serreEps_neg_padicIntUnitFive : serreEps (-padicIntUnitFive) = 1 := by
  rw [neg_eq_neg_one_mul, serreEps_mul, serreEps_neg_one,
    serreEps_eq_zero_of_coe_eq_five val_padicIntUnitFive, add_zero]

/-- `δ(5) = 2` over `ℚ₂`: the approximation `5 − 1² = 4` attains the upper bound `2 v(2)` of
the defect exponent of a nonsquare unit. -/
private theorem defectExponent_five :
    defectExponent (Units.mk0 (5 : ℚ_[2]) (by norm_num)) = 2 := by
  have hsq : ¬IsSquare (Units.mk0 (5 : ℚ_[2]) (by norm_num)) :=
    fun h => Padic.not_isSquare_five (isSquare_units_val_iff.mpr h)
  have hval : valuation ℚ_[2] ((Units.mk0 (5 : ℚ_[2]) (by norm_num) : ℚ_[2]ˣ) : ℚ_[2]) = 1 :=
    Padic.valuation_eq_one_of_coe_eq (u := padicIntUnitFive) coe_padicIntUnitFive.symm
  refine le_antisymm ?_ ?_
  · simpa [Padic.natCastValuation_self 2] using
      defectExponent_le_two_mul_natCastValuation two_ne_zero hval hsq
  · have h := le_defectExponent (Units.mk0 (5 : ℚ_[2]) (by norm_num)) 1
      (Units.mk0 (((2 : ℕ) : ℚ_[2]) ^ 2) (by simp)) (by norm_num)
    rwa [_root_.Padic.toAdd_normalizedValuation_mk0_natCast_pow] at h

/-- **The units of maximal defect over `ℚ₂`.** If `u ∈ ℤ₂ˣ` is `5 mod 8`, that is `ε(u) = 0`
and `ω(u) = 1`, then its defect exponent is `2 = 2 v(2)`. -/
theorem defectExponent_of_serreEps_eq_zero_of_serreOmega_eq_one_padicTwo {a : ℚ_[2]ˣ} {u : ℤ_[2]ˣ}
    (ha : (a : ℚ_[2]) = u) (hε : serreEps u = 0) (hω : serreOmega u = 1) :
    defectExponent a = 2 := by
  -- Up to the square of a unit `w`, `u` is `5`.
  obtain ⟨w, hw⟩ := exists_eq_neg_one_pow_mul_five_pow_mul_sq u
  have hw' : ((Units.map PadicInt.Coe.ringHom.toMonoidHom w : ℚ_[2]ˣ) : ℚ_[2]) = w :=
    (Units.coe_map _ w).trans (PadicInt.Coe.ringHom_apply _)
  have h5 : ((5 : ℤ_[2]) : ℚ_[2]) = 5 := by norm_cast
  have hfive : a = Units.mk0 (5 : ℚ_[2]) (by norm_num) *
      Units.map PadicInt.Coe.ringHom.toMonoidHom w ^ 2 := by
    ext
    rw [ha, hw, hε, hω]
    push_cast [h5, hw', ZMod.val_zero, ZMod.val_one, Units.val_mk0]
    ring
  rw [hfive, defectExponent_mul_sq, defectExponent_five,
    _root_.Padic.toAdd_normalizedValuation_eq_zero_of_coe_eq hw']
  norm_num

/-- **The units of odd defect over `ℚ₂`.** If `u ∈ ℤ₂ˣ` is `3 mod 4`, that is `ε(u) = 1`, then
its defect exponent is `1`. -/
theorem defectExponent_of_serreEps_eq_one_padicTwo {a : ℚ_[2]ˣ} {u : ℤ_[2]ˣ}
    (ha : (a : ℚ_[2]) = u) (hε : serreEps u = 1) :
    defectExponent a = 1 := by
  have hval := Padic.valuation_eq_one_of_coe_eq ha
  have hsq : ¬IsSquare a := by
    rw [isSquare_iff_serreEps_eq_zero_and_serreOmega_eq_zero ha, hε]
    simp
  rcases defectExponent_eq_two_mul_natCastValuation_or_odd two_ne_zero hval hsq with h | ⟨k, hk, h⟩
  · -- Two units of maximal defect differ by a square, but `ε(5 u) = 1` says `5 u` is not one.
    have h5 : defectExponent (Units.mk0 (5 : ℚ_[2]) (by norm_num)) =
        ((2 * natCastValuation ℚ_[2] 2 two_ne_zero : ℕ) : ℤ) := by
      rw [defectExponent_five, Padic.natCastValuation_self 2]
      norm_num
    have hprod := isSquare_mul_of_defectExponent_eq_two_mul two_ne_zero hval
      (Padic.valuation_eq_one_of_coe_eq (u := padicIntUnitFive) coe_padicIntUnitFive.symm) h h5
    have hcoe : ((a * Units.mk0 (5 : ℚ_[2]) (by norm_num) : ℚ_[2]ˣ) : ℚ_[2]) =
        ((u * padicIntUnitFive : ℤ_[2]ˣ) : ℤ_[2]) := by
      simp [ha, coe_padicIntUnitFive]
    rw [isSquare_iff_serreEps_eq_zero_and_serreOmega_eq_zero hcoe, serreEps_mul, hε,
      serreEps_eq_zero_of_coe_eq_five val_padicIntUnitFive] at hprod
    simp at hprod
  · rw [Padic.natCastValuation_self 2] at hk
    obtain rfl : k = 0 := by omega
    exact h

/-- The defect exponent of a unit `u` of `ℤ₂`, read in `ℚ₂`: it is `1` when `u ≡ 3 mod 4`, `2`
when `u ≡ 5 mod 8`, and `⊤` when `u ≡ 1 mod 8`. -/
private theorem defectExponent_padicTwo_of_coe_eq {a : ℚ_[2]ˣ} {u : ℤ_[2]ˣ}
    (ha : (a : ℚ_[2]) = u) :
    defectExponent a = if serreEps u = 1 then 1 else if serreOmega u = 1 then 2 else ⊤ := by
  have key : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases key (serreEps u) with he | he
  · rcases key (serreOmega u) with ho | ho
    · simp only [he, ho, zero_ne_one, ↓reduceIte]
      exact defectExponent_eq_top_iff.mpr
        ((isSquare_iff_serreEps_eq_zero_and_serreOmega_eq_zero ha).mpr ⟨he, ho⟩)
    · simp only [he, ho, zero_ne_one, ↓reduceIte]
      exact defectExponent_of_serreEps_eq_zero_of_serreOmega_eq_one_padicTwo ha he ho
  · simp only [he, ↓reduceIte]
    exact defectExponent_of_serreEps_eq_one_padicTwo ha he

/-- **The defect exponent over `ℚ₂`.** For `a = 2 ^ α u` with `u` a unit of `ℤ₂`, the defect
exponent `δ(a)` is `α` when `α` is odd. When `α` is even it is `α + 1` if `u ≡ 3 mod 4`, that is
`ε(u) = 1`, it is `α + 2` if `u ≡ 5 mod 8`, and it is `⊤`, so that `a` is a square, if
`u ≡ 1 mod 8`. -/
theorem defectExponent_padicTwo {a : ℚ_[2]ˣ} {α : ℤ} {u : ℤ_[2]ˣ}
    (ha : (a : ℚ_[2]) = 2 ^ α * u) :
    defectExponent a = if Odd α then (α : WithTop ℤ) else
      if serreEps u = 1 then (α + 1 : ℤ) else if serreOmega u = 1 then (α + 2 : ℤ) else ⊤ := by
  -- The defects of `±1` and `±5` come from the general theory; the square factor and the power
  -- of `2` are moved with `defectExponent_mul_sq` and `defectExponent_of_odd`.
  have hv : (normalizedValuation ℚ_[2] a).toAdd = α := by
    have h := _root_.Padic.valuation_p_zpow_mul (p := 2) α (PadicInt.coe_ne_zero.mpr u.ne_zero)
    rw [PadicInt.valuation_coe, PadicInt.valuation_eq_zero_of_isUnit u.isUnit, Nat.cast_zero,
      add_zero] at h
    rw [_root_.Padic.toAdd_normalizedValuation_eq_valuation, ha]
    exact_mod_cast h
  by_cases hα : Odd α
  · simp only [hα, ↓reduceIte]
    rw [defectExponent_of_odd (hv ▸ hα), hv]
  -- For `α = 2m`, `a` is the unit `u` times the square of `2 ^ m`.
  obtain ⟨m, rfl⟩ := Int.not_odd_iff_even.mp hα
  let u' : ℚ_[2]ˣ := Units.mk0 ((u : ℤ_[2]) : ℚ_[2]) (PadicInt.coe_ne_zero.mpr u.ne_zero)
  let t : ℚ_[2]ˣ := Units.mk0 (2 ^ m) (zpow_ne_zero _ two_ne_zero)
  have hat : a = u' * t ^ 2 := Units.ext <| by
    simp only [ha, u', t, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [zpow_add₀ two_ne_zero]
    ring
  have ht : (normalizedValuation ℚ_[2] t).toAdd = m := by
    simp [t]
  simp only [hα, ↓reduceIte]
  rw [hat, defectExponent_mul_sq, ht, defectExponent_padicTwo_of_coe_eq rfl]
  split_ifs
  · rw [← WithTop.coe_one, ← WithTop.coe_add]
    congr 1
    ring
  · rw [← WithTop.coe_ofNat, ← WithTop.coe_add]
    congr 1
    ring
  · exact WithTop.top_add _

/-- **The defect exponents of the square classes of `ℚ₂`.** On the representatives
`1, -1, 5, -5, 2, -2, 10, -10` of `TauCeti.padicTwoSquareClassRep`, the defect exponent takes the
values `⊤, 1, 2, 1, 1, 1, 1, 1`. -/
@[simp]
theorem defectExponent_padicTwoSquareClassRep (i : Fin 8) :
    defectExponent (padicTwoSquareClassRep i) = ![⊤, 1, 2, 1, 1, 1, 1, 1] i := by
  have hodd : ∀ {a : ℚ_[2]ˣ} {m : ℤ}, ¬((2 : ℕ) : ℤ) ∣ m →
      (a : ℚ_[2]) = ((2 : ℕ) : ℚ_[2]) ^ 1 * (m : ℚ_[2]) → defectExponent a = 1 :=
    fun {a} {m} hm ha ↦ by
    have hv : (normalizedValuation ℚ_[2] a).toAdd = 1 := by
      rw [_root_.Padic.toAdd_normalizedValuation_eq_valuation, ha,
        _root_.Padic.valuation_p_pow_mul_intCast 1 hm, Nat.cast_one]
    rw [defectExponent_of_odd (hv ▸ odd_one), hv, WithTop.coe_one]
  fin_cases i
  · exact defectExponent_eq_top_iff.mpr (isSquare_units_val_iff.mp ⟨1, by simp⟩)
  · exact defectExponent_of_serreEps_eq_one_padicTwo (u := -1) (by simp) serreEps_neg_one
  · exact defectExponent_of_serreEps_eq_zero_of_serreOmega_eq_one_padicTwo (u := padicIntUnitFive)
      (by simp [coe_padicIntUnitFive]) (serreEps_eq_zero_of_coe_eq_five val_padicIntUnitFive)
      (serreOmega_eq_one_of_coe_eq_five val_padicIntUnitFive)
  · exact defectExponent_of_serreEps_eq_one_padicTwo (u := -padicIntUnitFive)
      (by simp [coe_padicIntUnitFive]) serreEps_neg_padicIntUnitFive
  · exact hodd (m := 1) (by decide) (by simp)
  · exact hodd (m := -1) (by decide) (by simp)
  · exact hodd (m := 5) (by decide) (by simp; norm_num)
  · exact hodd (m := -5) (by decide) (by simp; norm_num)

/-- **The quadratic defects of the square classes of `ℚ₂`.** On the representatives
`1, -1, 5, -5, 2, -2, 10, -10` of `TauCeti.padicTwoSquareClassRep`, the quadratic defect is
`0, 2 ℤ₂, 4 ℤ₂, 2 ℤ₂, 2 ℤ₂, 2 ℤ₂, 2 ℤ₂, 2 ℤ₂`. In particular the units `1`, `5` and `-1`
attain the three defects `0`, `4 ℤ₂` and `2 ℤ₂` of units of `ℤ₂`. -/
@[simp]
theorem quadraticDefect_padicTwoSquareClassRep (i : Fin 8) :
    quadraticDefect (padicTwoSquareClassRep i) =
      FractionalIdeal.spanSingleton _ (![0, 2, 4, 2, 2, 2, 2, 2] i) := by
  -- `2` and `4` as units of `ℚ₂`, with valuations `1` and `2`.
  let c : ℕ → ℚ_[2]ˣ := fun k ↦ Units.mk0 (((2 : ℕ) : ℚ_[2]) ^ k) (by simp)
  have hc : ∀ k, (normalizedValuation ℚ_[2] (c k)).toAdd = k := fun k ↦
    _root_.Padic.toAdd_normalizedValuation_mk0_natCast_pow 2 k _
  fin_cases i
  · simp [quadraticDefect_eq_zero_iff, ← defectExponent_eq_top_iff]
  case «2» =>
    rw [quadraticDefect_eq_spanSingleton_of_defectExponent_eq (c := c 2) (by simp [hc])]
    norm_num [c]
  all_goals
    rw [quadraticDefect_eq_spanSingleton_of_defectExponent_eq (c := c 1) (by simp [hc])]
    norm_num [c]

/-- **The square units of `ℤ₂` have defect zero.** A unit `u` of `ℤ₂` has quadratic defect `0`
in `ℚ₂` if and only if `u ≡ 1 mod 8`, that is `ε(u) = ω(u) = 0`. -/
theorem quadraticDefect_eq_zero_iff_padicTwo {a : ℚ_[2]ˣ} {u : ℤ_[2]ˣ}
    (ha : (a : ℚ_[2]) = u) :
    quadraticDefect a = 0 ↔ serreEps u = 0 ∧ serreOmega u = 0 := by
  rw [quadraticDefect_eq_zero_iff, isSquare_iff_serreEps_eq_zero_and_serreOmega_eq_zero ha]

/-- **The units of maximal defect over `ℚ₂`, as ideals.** If `u ∈ ℤ₂ˣ` is `5 mod 8`, that is
`ε(u) = 0` and `ω(u) = 1`, then `𝔡(u) = 4 ℤ₂`. -/
theorem quadraticDefect_of_serreEps_eq_zero_of_serreOmega_eq_one_padicTwo {a : ℚ_[2]ˣ}
    {u : ℤ_[2]ˣ} (ha : (a : ℚ_[2]) = u) (hε : serreEps u = 0) (hω : serreOmega u = 1) :
    quadraticDefect a = FractionalIdeal.spanSingleton _ 4 := by
  rw [quadraticDefect_eq_maximalIdeal_zpow
      (defectExponent_of_serreEps_eq_zero_of_serreOmega_eq_one_padicTwo ha hε hω),
    show (4 : ℚ_[2]) = ((2 : ℕ) : ℚ_[2]) ^ 2 by norm_num,
    Padic.spanSingleton_natCast_pow_eq_maximalIdeal_zpow]

/-- **The units of odd defect over `ℚ₂`, as ideals.** If `u ∈ ℤ₂ˣ` is `3 mod 4`, that is
`ε(u) = 1`, then `𝔡(u) = 2 ℤ₂`. -/
theorem quadraticDefect_of_serreEps_eq_one_padicTwo {a : ℚ_[2]ˣ} {u : ℤ_[2]ˣ}
    (ha : (a : ℚ_[2]) = u) (hε : serreEps u = 1) :
    quadraticDefect a = FractionalIdeal.spanSingleton _ 2 := by
  rw [quadraticDefect_eq_maximalIdeal_zpow (defectExponent_of_serreEps_eq_one_padicTwo ha hε),
    show (2 : ℚ_[2]) = ((2 : ℕ) : ℚ_[2]) ^ 1 by norm_num,
    Padic.spanSingleton_natCast_pow_eq_maximalIdeal_zpow, Nat.cast_one]

/-- `𝔡(5) = 4 ℤ₂` over `ℚ₂`. -/
theorem quadraticDefect_five_padicTwo :
    quadraticDefect (Units.mk0 (5 : ℚ_[2]) (by norm_num)) = FractionalIdeal.spanSingleton _ 4 :=
  quadraticDefect_of_serreEps_eq_zero_of_serreOmega_eq_one_padicTwo (u := padicIntUnitFive)
    coe_padicIntUnitFive.symm
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
    (by simp [coe_padicIntUnitFive]) serreEps_neg_padicIntUnitFive

/-- **The quadratic defect is not multiplicative.** Over `ℚ₂`, `𝔡(-1) = 2 ℤ₂` and `𝔡(5) = 4 ℤ₂`,
but `𝔡(-1 · 5) = 𝔡(-5) = 2 ℤ₂` is not `8 ℤ₂`. -/
theorem quadraticDefect_neg_one_mul_five_ne_mul_padicTwo :
    quadraticDefect (-1 * Units.mk0 (5 : ℚ_[2]) (by norm_num)) ≠
      quadraticDefect (-1) * quadraticDefect (Units.mk0 (5 : ℚ_[2]) (by norm_num)) := by
  rw [neg_one_mul, quadraticDefect_neg_five_padicTwo, quadraticDefect_neg_one_padicTwo,
    quadraticDefect_five_padicTwo, ← map_mul]
  intro h
  -- Comparing valuations, `2 ℤ₂ ⊆ 8 ℤ₂` would give `v(8) ≤ v(2)`, that is `3 ≤ 1`.
  have hle := (toAdd_normalizedValuation_le_iff_valuation_le
    (Units.mk0 (((2 : ℕ) : ℚ_[2]) ^ 3) (by simp)) (Units.mk0 (((2 : ℕ) : ℚ_[2]) ^ 1) (by simp))).mpr
      (by simpa [show (2 : ℚ_[2]) * 4 = 2 ^ 3 by norm_num] using
        spanSingleton_le_spanSingleton_iff_valuation_le.mp h.le)
  rw [_root_.Padic.toAdd_normalizedValuation_mk0_natCast_pow,
    _root_.Padic.toAdd_normalizedValuation_mk0_natCast_pow] at hle
  omega

end TauCeti
