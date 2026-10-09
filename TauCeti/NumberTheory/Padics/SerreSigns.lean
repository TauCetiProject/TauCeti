/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.IntUnitsPower
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import TauCeti.NumberTheory.Padics.PrincipalUnits
import TauCeti.NumberTheory.Padics.DyadicUnits

/-!
# Serre's sign functions on `ℤ_2ˣ` and the square classes of `2`-adic units

For a unit `u` of `ℤ_2`, Serre (*A Course in Arithmetic*, Chapter I, §3.2) puts

* `ε(u) = (u − 1)/2 mod 2`, and
* `ω(u) = (u² − 1)/8 mod 2`.

Both depend only on `u mod 8`: on the odd residues `1, 3, 5, 7` they take the values
`ε = 0, 1, 0, 1` and `ω = 0, 1, 1, 0`. They are the `ZMod 2`-valued logarithms of the characters
`ZMod.χ₄` and `ZMod.χ₈` of Mathlib, and they are the exponents in Serre's closed formula for the
Hilbert symbol over `ℚ_2`.

The point of `ε` and `ω` is that together they classify `2`-adic units up to squares. A unit is
the square of a unit exactly when it is `1 mod 8`, and every unit `u` satisfies

`u = (-1) ^ ε(u) · 5 ^ ω(u) · w²`

for some unit `w`. Read in `ℚ_2`, a unit of `ℤ_2` is a square of `ℚ_2` exactly when it is
`1 mod 8`.

## Main definitions

* `TauCeti.serreEps`: Serre's `ε : ℤ_2ˣ → ZMod 2`.
* `TauCeti.serreOmega`: Serre's `ω : ℤ_2ˣ → ZMod 2`.

## Main results

* `TauCeti.serreEps_eq_one_iff`, `TauCeti.serreOmega_eq_one_iff` (and the `_eq_zero_iff`
  variants): the values of `ε` and `ω` in terms of `u mod 8`.
* `TauCeti.serreEps_mul`, `TauCeti.serreOmega_mul`: `ε` and `ω` are homomorphisms to the
  additive group `ZMod 2`; `TauCeti.serreEps_pow`, `TauCeti.serreOmega_pow` are the power forms.
* `TauCeti.coe_neg_one_uzpow_serreEps`, `TauCeti.coe_neg_one_uzpow_serreOmega`: `(-1) ^ ε(u)` is
  `χ₄(u mod 4)` and `(-1) ^ ω(u)` is `χ₈(u mod 8)`.
* `TauCeti.serreEps_eq_zero_and_serreOmega_eq_zero_iff`: `ε(u) = ω(u) = 0` exactly when
  `u ≡ 1 mod 8`.
* `TauCeti.exists_eq_neg_one_pow_mul_five_pow_mul_sq`: `u = (-1) ^ ε(u) · 5 ^ ω(u) · w²`.
* `TauCeti.isSquare_coe_iff_mem_unitsPrincipal_three`: a unit of `ℤ_2` is a square in `ℚ_2`
  exactly when it lies in `U^(3) = 1 + 8ℤ_2`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter I, §3.2, Chapter II, §3.3, and Chapter III,
  §1.2.
-/

public section

namespace TauCeti

/-- Serre's `ε(u) = (u − 1)/2 mod 2` for a unit `u` of `ℤ_2`, read off `u mod 8`. On the odd
residues `1, 3, 5, 7` it takes the values `0, 1, 0, 1`. -/
noncomputable def serreEps (u : ℤ_[2]ˣ) : ZMod 2 :=
  if PadicInt.toZModPow 3 (u : ℤ_[2]) = 3 ∨ PadicInt.toZModPow 3 (u : ℤ_[2]) = 7 then 1 else 0

/-- Serre's `ω(u) = (u² − 1)/8 mod 2` for a unit `u` of `ℤ_2`, read off `u mod 8`. On the odd
residues `1, 3, 5, 7` it takes the values `0, 1, 1, 0`. -/
noncomputable def serreOmega (u : ℤ_[2]ˣ) : ZMod 2 :=
  if PadicInt.toZModPow 3 (u : ℤ_[2]) = 3 ∨ PadicInt.toZModPow 3 (u : ℤ_[2]) = 5 then 1 else 0

/-- The residue of a unit of `ℤ_2` modulo `8` is invertible. -/
private theorem exists_toZModPow_three_mul_eq_one (u : ℤ_[2]ˣ) :
    ∃ y, PadicInt.toZModPow 3 (u : ℤ_[2]) * y = 1 :=
  ⟨PadicInt.toZModPow 3 ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]), by rw [← map_mul, Units.mul_inv, map_one]⟩

/-- `ε` is a homomorphism from `ℤ_2ˣ` to the additive group `ZMod 2`. -/
theorem serreEps_mul (u v : ℤ_[2]ˣ) : serreEps (u * v) = serreEps u + serreEps v := by
  have key : ∀ x x' : ZMod (2 ^ 3), (∃ y, x * y = 1) → (∃ y, x' * y = 1) →
      (if x * x' = 3 ∨ x * x' = 7 then (1 : ZMod 2) else 0) =
        (if x = 3 ∨ x = 7 then 1 else 0) + (if x' = 3 ∨ x' = 7 then 1 else 0) := by
    decide
  simpa only [serreEps, Units.val_mul, map_mul] using
    key _ _ (exists_toZModPow_three_mul_eq_one u) (exists_toZModPow_three_mul_eq_one v)

/-- `ω` is a homomorphism from `ℤ_2ˣ` to the additive group `ZMod 2`. -/
theorem serreOmega_mul (u v : ℤ_[2]ˣ) : serreOmega (u * v) = serreOmega u + serreOmega v := by
  have key : ∀ x x' : ZMod (2 ^ 3), (∃ y, x * y = 1) → (∃ y, x' * y = 1) →
      (if x * x' = 3 ∨ x * x' = 5 then (1 : ZMod 2) else 0) =
        (if x = 3 ∨ x = 5 then 1 else 0) + (if x' = 3 ∨ x' = 5 then 1 else 0) := by
    decide
  simpa only [serreOmega, Units.val_mul, map_mul] using
    key _ _ (exists_toZModPow_three_mul_eq_one u) (exists_toZModPow_three_mul_eq_one v)

/-- `ε(u) = 1` exactly when `u` is `3` or `7` modulo `8`. -/
theorem serreEps_eq_one_iff (u : ℤ_[2]ˣ) :
    serreEps u = 1 ↔
      PadicInt.toZModPow 3 (u : ℤ_[2]) = 3 ∨ PadicInt.toZModPow 3 (u : ℤ_[2]) = 7 := by
  unfold serreEps
  split_ifs with h <;> simp [h]

/-- `ε(u) = 0` exactly when `u` is `1` or `5` modulo `8`. -/
theorem serreEps_eq_zero_iff (u : ℤ_[2]ˣ) :
    serreEps u = 0 ↔
      PadicInt.toZModPow 3 (u : ℤ_[2]) = 1 ∨ PadicInt.toZModPow 3 (u : ℤ_[2]) = 5 := by
  have key : ∀ x : ZMod (2 ^ 3), (∃ y, x * y = 1) →
      ((if x = 3 ∨ x = 7 then (1 : ZMod 2) else 0) = 0 ↔ x = 1 ∨ x = 5) := by
    decide
  exact key _ (exists_toZModPow_three_mul_eq_one u)

/-- `ω(u) = 1` exactly when `u` is `3` or `5` modulo `8`. -/
theorem serreOmega_eq_one_iff (u : ℤ_[2]ˣ) :
    serreOmega u = 1 ↔
      PadicInt.toZModPow 3 (u : ℤ_[2]) = 3 ∨ PadicInt.toZModPow 3 (u : ℤ_[2]) = 5 := by
  unfold serreOmega
  split_ifs with h <;> simp [h]

/-- `ω(u) = 0` exactly when `u` is `1` or `7` modulo `8`. -/
theorem serreOmega_eq_zero_iff (u : ℤ_[2]ˣ) :
    serreOmega u = 0 ↔
      PadicInt.toZModPow 3 (u : ℤ_[2]) = 1 ∨ PadicInt.toZModPow 3 (u : ℤ_[2]) = 7 := by
  have key : ∀ x : ZMod (2 ^ 3), (∃ y, x * y = 1) →
      ((if x = 3 ∨ x = 5 then (1 : ZMod 2) else 0) = 0 ↔ x = 1 ∨ x = 7) := by
    decide
  exact key _ (exists_toZModPow_three_mul_eq_one u)

/-- `5` is a unit of `ℤ_2`. -/
theorem isUnit_five_padicInt : IsUnit (5 : ℤ_[2]) := by
  rw [PadicInt.isUnit_iff]
  exact_mod_cast PadicInt.norm_natCast_eq_one_iff.mpr (by norm_num)

/-- `ε(5) = 0`, for the unit `5` of `ℤ_2`. -/
theorem serreEps_eq_zero_of_coe_eq_five {u : ℤ_[2]ˣ} (hu : (u : ℤ_[2]) = 5) :
    serreEps u = 0 := by
  have h : ¬((5 : ZMod (2 ^ 3)) = 3 ∨ (5 : ZMod (2 ^ 3)) = 7) := by decide
  simp [serreEps, hu, map_ofNat, h]

/-- `ω(5) = 1`, for the unit `5` of `ℤ_2`. -/
theorem serreOmega_eq_one_of_coe_eq_five {u : ℤ_[2]ˣ} (hu : (u : ℤ_[2]) = 5) :
    serreOmega u = 1 := by
  simp [serreOmega, hu, map_ofNat]

/-- `ε(1) = 0`. -/
@[simp]
theorem serreEps_one : serreEps 1 = 0 := by
  have h : ¬((1 : ZMod (2 ^ 3)) = 3 ∨ (1 : ZMod (2 ^ 3)) = 7) := by decide
  simp [serreEps, h]

/-- `ω(1) = 0`. -/
@[simp]
theorem serreOmega_one : serreOmega 1 = 0 := by
  have h : ¬((1 : ZMod (2 ^ 3)) = 3 ∨ (1 : ZMod (2 ^ 3)) = 5) := by decide
  simp [serreOmega, h]

/-- `ε(u ^ n) = n ε(u)`. -/
theorem serreEps_pow (u : ℤ_[2]ˣ) (n : ℕ) : serreEps (u ^ n) = n • serreEps u := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, serreEps_mul, ih, succ_nsmul]

/-- `ω(u ^ n) = n ω(u)`. -/
theorem serreOmega_pow (u : ℤ_[2]ˣ) (n : ℕ) : serreOmega (u ^ n) = n • serreOmega u := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, serreOmega_mul, ih, succ_nsmul]

/-- `ε(-1) = 1`. -/
@[simp]
theorem serreEps_neg_one : serreEps (-1) = 1 := by
  have h : (-1 : ZMod (2 ^ 3)) = 7 := by decide
  simp [serreEps, h]

/-- `ω(-1) = 0`. -/
@[simp]
theorem serreOmega_neg_one : serreOmega (-1) = 0 := by
  have h : ¬((-1 : ZMod (2 ^ 3)) = 3 ∨ (-1 : ZMod (2 ^ 3)) = 5) := by decide
  simp [serreOmega, h]

/-- The sign `(-1) ^ ε(u)` is Mathlib's character `χ₄` of `u mod 4`. -/
theorem coe_neg_one_uzpow_serreEps (u : ℤ_[2]ˣ) :
    (((-1 : ℤˣ) ^ serreEps u : ℤˣ) : ℤ) = ZMod.χ₄ (PadicInt.toZModPow 2 (u : ℤ_[2])) := by
  have key : ∀ x : ZMod (2 ^ 3), (∃ y, x * y = 1) →
      (((-1 : ℤˣ) ^ (if x = 3 ∨ x = 7 then (1 : ZMod 2) else 0) : ℤˣ) : ℤ) =
        ZMod.χ₄ (ZMod.castHom (pow_dvd_pow 2 (by norm_num : 2 ≤ 3)) (ZMod (2 ^ 2)) x) := by
    decide
  rw [← PadicInt.cast_toZModPow 2 3 (by norm_num)]
  exact key _ (exists_toZModPow_three_mul_eq_one u)

/-- The sign `(-1) ^ ω(u)` is Mathlib's character `χ₈` of `u mod 8`. -/
theorem coe_neg_one_uzpow_serreOmega (u : ℤ_[2]ˣ) :
    (((-1 : ℤˣ) ^ serreOmega u : ℤˣ) : ℤ) = ZMod.χ₈ (PadicInt.toZModPow 3 (u : ℤ_[2])) := by
  have key : ∀ x : ZMod (2 ^ 3), (∃ y, x * y = 1) →
      (((-1 : ℤˣ) ^ (if x = 3 ∨ x = 5 then (1 : ZMod 2) else 0) : ℤˣ) : ℤ) = ZMod.χ₈ x := by
    decide
  exact key _ (exists_toZModPow_three_mul_eq_one u)

/-- `ε` and `ω` both vanish exactly on the units `U^(3)` that are `1 mod 8`, which are the squares
of `ℤ_2ˣ` by `TauCeti.unitsPrincipal_three_eq_range_powMonoidHom_two`. -/
theorem serreEps_eq_zero_and_serreOmega_eq_zero_iff (u : ℤ_[2]ˣ) :
    serreEps u = 0 ∧ serreOmega u = 0 ↔ u ∈ unitsPrincipal 2 3 := by
  have key : ∀ x : ZMod (2 ^ 3), (∃ y, x * y = 1) →
      ((if x = 3 ∨ x = 7 then (1 : ZMod 2) else 0) = 0 ∧
        (if x = 3 ∨ x = 5 then (1 : ZMod 2) else 0) = 0 ↔ x = 1) := by
    decide
  rw [mem_unitsPrincipal_iff_toZModPow]
  exact key _ (exists_toZModPow_three_mul_eq_one u)

/-- **The square classes of `ℤ_2ˣ`.** Every unit `u` of `ℤ_2` is `(-1) ^ ε(u) · 5 ^ ω(u)` times
the square of a unit. -/
theorem exists_eq_neg_one_pow_mul_five_pow_mul_sq (u : ℤ_[2]ˣ) :
    ∃ w : ℤ_[2]ˣ, (u : ℤ_[2]) = (-1) ^ (serreEps u).val * 5 ^ (serreOmega u).val * w ^ 2 := by
  set r : ℤ_[2] := (-1) ^ (serreEps u).val * 5 ^ (serreOmega u).val
  have hr : IsUnit r := ((isUnit_neg_one.pow _).mul (isUnit_five_padicInt.pow _))
  have key : ∀ x : ZMod (2 ^ 3), (∃ y, x * y = 1) →
      x = (-1) ^ (if x = 3 ∨ x = 7 then (1 : ZMod 2) else 0).val *
        5 ^ (if x = 3 ∨ x = 5 then (1 : ZMod 2) else 0).val := by
    decide
  -- `u` and `r` have the same residue modulo `8`, so `u r⁻¹ ∈ U^(3)` is a square.
  have hres : PadicInt.toZModPow 3 (u : ℤ_[2]) = PadicInt.toZModPow 3 r := by
    simpa [r, serreEps, serreOmega, map_ofNat] using key _ (exists_toZModPow_three_mul_eq_one u)
  have hmem : u * hr.unit⁻¹ ∈ unitsPrincipal 2 3 := by
    rw [mem_unitsPrincipal_iff_toZModPow, Units.val_mul, map_mul, hres, ← map_mul,
      IsUnit.mul_val_inv, map_one]
  rw [unitsPrincipal_three_eq_range_powMonoidHom_two] at hmem
  obtain ⟨w, hw⟩ := hmem
  refine ⟨w, ?_⟩
  rw [powMonoidHom_apply, eq_mul_inv_iff_mul_eq] at hw
  rw [← hw, Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec, mul_comm]

/-- **Squares of `2`-adic units in `ℚ_2`.** A unit of `ℤ_2` is a square in `ℚ_2` exactly when it is
`1 mod 8`. -/
theorem isSquare_coe_iff_mem_unitsPrincipal_three (u : ℤ_[2]ˣ) :
    IsSquare ((u : ℤ_[2]) : ℚ_[2]) ↔ u ∈ unitsPrincipal 2 3 := by
  constructor
  · rintro ⟨b, hb⟩
    have hb1 : ‖b‖ = 1 := by
      have h : ‖b‖ * ‖b‖ = 1 := by
        rw [← norm_mul, ← hb, ← PadicInt.norm_def, PadicInt.norm_units]
      nlinarith [norm_nonneg b]
    have hc : (u : ℤ_[2]) = PadicInt.mkUnits hb1 * PadicInt.mkUnits hb1 :=
      PadicInt.ext (by push_cast [PadicInt.mkUnits_eq]; exact hb)
    have key : ∀ x z : ZMod (2 ^ 3), (∃ y, x * y = 1) → z * z = x → x = 1 := by decide
    rw [mem_unitsPrincipal_iff_toZModPow]
    exact key _ _ (exists_toZModPow_three_mul_eq_one u) (by rw [hc, map_mul])
  · intro hu
    rw [unitsPrincipal_three_eq_range_powMonoidHom_two] at hu
    obtain ⟨w, rfl⟩ := hu
    exact ⟨w, by simp [pow_two]⟩

end TauCeti
