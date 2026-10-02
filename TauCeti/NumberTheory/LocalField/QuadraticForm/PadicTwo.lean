/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HilbertSymbol.Basic
public import TauCeti.NumberTheory.Padics.SerreSigns
import Mathlib.NumberTheory.Padics.LocalField
import TauCeti.Algebra.Group.Units.Basic
import TauCeti.NumberTheory.LocalField.Padic
import TauCeti.NumberTheory.LocalField.QuadraticForm.Bimultiplicativity
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# The Hilbert symbol over `ℚ_2`

Write `a, b ∈ ℚ_2ˣ` as `a = 2 ^ α u` and `b = 2 ^ β v` with `u, v` units of `ℤ_2`. Serre's
closed formula for the Hilbert symbol over `ℚ_2` is

`(a, b) = (-1) ^ (ε(u) ε(v) + α ω(v) + β ω(u))`,

where `ε(u) = (u − 1)/2` and `ω(u) = (u² − 1)/8` modulo `2` are the sign functions
`TauCeti.serreEps` and `TauCeti.serreOmega`. The exponent lives in `ZMod 2`, and the sign is
`(-1 : ℤˣ) ^ x` for `x : ZMod 2`. This is the one dyadic field on which the symbol has a closed
formula, and it pins down the sign convention of the local Hilbert symbol in residue
characteristic `2`.

The classes of `-1`, `2` and `5` generate `ℚ_2ˣ/(ℚ_2ˣ)²`, since every unit of `ℤ_2` is
`(-1) ^ ε(u) 5 ^ ω(u)` times a square (`TauCeti.exists_eq_neg_one_pow_mul_five_pow_mul_sq`). On
these generators the symbol takes the values

* `(-1, 2) = (-1, 5) = (2, 2) = (5, 5) = +1`, and
* `(-1, -1) = (2, 5) = −1`.

## Main results

* `TauCeti.hilbertSymbol_padicTwo`: Serre's formula for the Hilbert symbol over `ℚ_2`.
* `TauCeti.hilbertSymbol_neg_one_neg_one_padicTwo`: `(-1, -1) = −1` over `ℚ_2`, that is `-1` is
  not of the form `x² + y²` in `ℚ_2`.
* `TauCeti.hilbertSymbol_two_five_padicTwo`: `(2, 5) = −1` over `ℚ_2`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1.2, Theorem 1.
-/

public section

namespace TauCeti

/-- `2` as a unit of `ℚ_2`. -/
private noncomputable abbrev unitTwo : ℚ_[2]ˣ := Units.mk0 2 two_ne_zero

/-- `5` as a unit of `ℚ_2`. -/
private noncomputable abbrev unitFive : ℚ_[2]ˣ := Units.mk0 5 (by norm_num)

private theorem two_ne_zero_padicTwo : (2 : ℚ_[2]) ≠ 0 := two_ne_zero

private noncomputable instance : Invertible (2 : ℚ_[2]) := invertibleOfNonzero two_ne_zero_padicTwo

/-- A unit of `ℤ_2`, read in `ℚ_2ˣ`, is `(-1) ^ ε(u) 5 ^ ω(u)` times a square. -/
private theorem exists_eq_neg_one_zpow_mul_unitFive_zpow_mul_sq {a : ℚ_[2]ˣ} {u : ℤ_[2]ˣ}
    (ha : (a : ℚ_[2]) = u) :
    ∃ w : ℚ_[2]ˣ,
      a = (-1) ^ ((serreEps u).val : ℤ) * unitFive ^ ((serreOmega u).val : ℤ) * w ^ 2 := by
  obtain ⟨w, hw⟩ := exists_eq_neg_one_pow_mul_five_pow_mul_sq u
  have hw0 : ((w : ℤ_[2]) : ℚ_[2]) ≠ 0 := PadicInt.coe_ne_zero.mpr w.ne_zero
  refine ⟨Units.mk0 _ hw0, Units.ext ?_⟩
  rw [ha, hw]
  simp only [Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one, Units.val_mk0]
  norm_cast

/-- Expansion of the symbol in its second argument along the generators `2`, `-1`, `5`. -/
private theorem hilbertSymbol_eq_of_eq_two_zpow_mul (c b : ℚ_[2]ˣ) {β : ℤ} {v : ℤ_[2]ˣ}
    (hb : (b : ℚ_[2]) = 2 ^ β * v) :
    hilbertSymbol c b = hilbertSymbol c unitTwo ^ β *
      hilbertSymbol c (-1) ^ ((serreEps v).val : ℤ) *
        hilbertSymbol c unitFive ^ ((serreOmega v).val : ℤ) := by
  have hv0 : ((v : ℤ_[2]) : ℚ_[2]) ≠ 0 := PadicInt.coe_ne_zero.mpr v.ne_zero
  obtain ⟨w, hw⟩ := exists_eq_neg_one_zpow_mul_unitFive_zpow_mul_sq (a := Units.mk0 _ hv0) rfl
  have hb' : b = unitTwo ^ β * Units.mk0 _ hv0 := Units.ext (by simp [hb])
  rw [hb', hw, hilbertSymbol_mul_right two_ne_zero_padicTwo, hilbertSymbol_mul_sq_right]
  simp only [hilbertSymbol_mul_right two_ne_zero_padicTwo,
    hilbertSymbol_zpow_right two_ne_zero_padicTwo, mul_assoc]

/-- Every element of `ℚ_2ˣ` is `2 ^ β` times a unit of `ℤ_2`. -/
private theorem exists_eq_two_zpow_mul (b : ℚ_[2]ˣ) :
    ∃ (β : ℤ) (v : ℤ_[2]ˣ), (b : ℚ_[2]) = 2 ^ β * v := by
  obtain ⟨v, hv⟩ := Padic.exists_eq_zpow_valuation_mul b.ne_zero
  exact ⟨_, v, by exact_mod_cast hv⟩

/-- A unit of `ℤ_2` that is not `1 mod 8` is a nonsquare of `ℚ_2ˣ`. -/
private theorem not_isSquare_of_toZModPow_ne_one {a : ℚ_[2]ˣ} {u : ℤ_[2]ˣ}
    (ha : (a : ℚ_[2]) = u) (hu : PadicInt.toZModPow 3 (u : ℤ_[2]) ≠ 1) : ¬IsSquare a := by
  rw [← isSquare_units_val_iff, ha, isSquare_coe_iff_mem_unitsPrincipal_three,
    mem_unitsPrincipal_iff_toZModPow]
  exact hu

/-- For a nonsquare `c`, the symbol `(c, ·)` is nontrivial on one of the generators `2`, `-1`,
`5` of `ℚ_2ˣ/(ℚ_2ˣ)²`. -/
private theorem not_hilbertSymbol_generators_eq_one {c : ℚ_[2]ˣ} (hc : ¬IsSquare c)
    (ht : hilbertSymbol c unitTwo = 1) (hm : hilbertSymbol c (-1) = 1)
    (hf : hilbertSymbol c unitFive = 1) : False := by
  -- Nondegeneracy gives `b` with `(c, b) = −1`; expanding `b` in the generators by
  -- bimultiplicativity, the three trivial values give `(c, b) = +1`.
  obtain ⟨b, hb⟩ := exists_hilbertSymbol_eq_neg_one two_ne_zero_padicTwo hc
  obtain ⟨β, v, hv⟩ := exists_eq_two_zpow_mul b
  rw [hilbertSymbol_eq_of_eq_two_zpow_mul c b hv, ht, hm, hf] at hb
  simp at hb

-- The `+1` values on the generators, from explicit solutions of `b = x² − a y²`.
private theorem hilbertSymbol_neg_one_unitTwo : hilbertSymbol (-1) unitTwo = 1 :=
  (hilbertSymbol_eq_one_iff _ _).mpr ⟨1, 1, by norm_num⟩

private theorem hilbertSymbol_neg_one_unitFive : hilbertSymbol (-1) unitFive = 1 :=
  (hilbertSymbol_eq_one_iff _ _).mpr ⟨1, 2, by norm_num⟩

private theorem hilbertSymbol_unitFive_unitFive : hilbertSymbol unitFive unitFive = 1 :=
  (hilbertSymbol_eq_one_iff _ _).mpr ⟨5, 2, by norm_num⟩

/-- `(-1, -1) = −1` over `ℚ_2`: `-1` is not of the form `x² + y²` with `x, y ∈ ℚ_2`. -/
theorem hilbertSymbol_neg_one_neg_one_padicTwo : hilbertSymbol (-1 : ℚ_[2]ˣ) (-1) = -1 := by
  -- `-1` is a nonsquare, and `(-1, 2) = (-1, 5) = +1`, so `(-1, -1)` must be `−1`.
  have hc : ¬IsSquare (-1 : ℚ_[2]ˣ) :=
    not_isSquare_of_toZModPow_ne_one (u := -1) (by simp)
      (by rw [Units.val_neg, Units.val_one, map_neg, map_one]; decide)
  exact (Int.units_eq_one_or _).resolve_left fun h ↦ not_hilbertSymbol_generators_eq_one hc
    hilbertSymbol_neg_one_unitTwo h hilbertSymbol_neg_one_unitFive

/-- `(2, 5) = −1` over `ℚ_2`: `5` is not of the form `x² − 2 y²` with `x, y ∈ ℚ_2`. -/
theorem hilbertSymbol_two_five_padicTwo :
    hilbertSymbol (Units.mk0 (2 : ℚ_[2]) two_ne_zero) (Units.mk0 5 (by norm_num)) = -1 := by
  -- `5` is a nonsquare, and `(5, -1) = (5, 5) = +1`, so `(5, 2)` must be `−1`.
  have hc : ¬IsSquare unitFive := by
    rw [← isSquare_units_val_iff]
    exact Padic.not_isSquare_five
  rw [hilbertSymbol_comm]
  exact (Int.units_eq_one_or _).resolve_left fun h ↦ not_hilbertSymbol_generators_eq_one hc h
    (by rw [hilbertSymbol_comm]; exact hilbertSymbol_neg_one_unitFive)
    hilbertSymbol_unitFive_unitFive

/-- **Serre's formula for the Hilbert symbol over `ℚ_2`.** For `a = 2 ^ α u` and `b = 2 ^ β v`
with `u, v` units of `ℤ_2`,

`(a, b) = (-1) ^ (ε(u) ε(v) + α ω(v) + β ω(u))`,

with the exponent computed in `ZMod 2`. -/
theorem hilbertSymbol_padicTwo {a b : ℚ_[2]ˣ} {α β : ℤ} {u v : ℤ_[2]ˣ}
    (ha : (a : ℚ_[2]) = 2 ^ α * u) (hb : (b : ℚ_[2]) = 2 ^ β * v) :
    hilbertSymbol a b = (-1 : ℤˣ) ^ (serreEps u * serreEps v + (α : ZMod 2) * serreOmega v +
      (β : ZMod 2) * serreOmega u) := by
  have h2m : hilbertSymbol unitTwo (-1) = 1 := by
    rw [hilbertSymbol_comm]
    exact hilbertSymbol_neg_one_unitTwo
  have h5m : hilbertSymbol unitFive (-1) = 1 := by
    rw [hilbertSymbol_comm]
    exact hilbertSymbol_neg_one_unitFive
  have h52 : hilbertSymbol unitFive unitTwo = -1 := by
    rw [hilbertSymbol_comm]
    exact hilbertSymbol_two_five_padicTwo
  -- The symbol of each generator `2`, `-1`, `5` against `a`.
  have hta : hilbertSymbol unitTwo a = (-1) ^ ((serreOmega u).val : ℤ) := by
    simp [hilbertSymbol_eq_of_eq_two_zpow_mul _ a ha, h2m, hilbertSymbol_two_five_padicTwo]
  have hma : hilbertSymbol (-1) a = (-1) ^ ((serreEps u).val : ℤ) := by
    simp [hilbertSymbol_eq_of_eq_two_zpow_mul _ a ha, hilbertSymbol_neg_one_unitTwo,
      hilbertSymbol_neg_one_neg_one_padicTwo, hilbertSymbol_neg_one_unitFive]
  have hfa : hilbertSymbol unitFive a = (-1) ^ α := by
    simp [hilbertSymbol_eq_of_eq_two_zpow_mul _ a ha, h52, h5m]
  rw [hilbertSymbol_eq_of_eq_two_zpow_mul a b hb, hilbertSymbol_comm a, hilbertSymbol_comm a,
    hilbertSymbol_comm a, hta, hma, hfa]
  simp only [← uzpow_intCast (R := ZMod 2), ← uzpow_mul, ← uzpow_add]
  congr 1
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  ring

end TauCeti
