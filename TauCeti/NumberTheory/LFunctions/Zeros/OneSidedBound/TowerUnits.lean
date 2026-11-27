/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Units
public import Mathlib.GroupTheory.OrderOfElement
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
import TauCeti.Data.ZMod.OrderOf

/-!
# A cyclic family of labels in the cyclotomic tower

At level `q₁ = q₀ · 3 · l₀ · 2 ^ s`, the unit `g = 1 + 3 · l₀ · q₀` has exact order `2 ^ s`
and reduces to `1` modulo `3 · l₀ · q₀`. Thus the negative powers `-g ^ e`, with `0 ≤ e < 2 ^ s`,
give distinct labels of class `-1` modulo `q₀`. A set of exponents avoiding modular mean
relations can be transported to place labels using this family.

The choice of the unit is from `New.Parameters.exists_orderOf_placeClass_eq` in
`grh/src/New/Reduction/Data/Existence.lean` of lsernau/grh-lean (`72fead1`).
-/

public section

namespace TauCeti.OneSidedBound.Parameters

variable (P : Parameters)

private theorem q₁_eq_base_mul_two_pow (s : ℕ) :
    P.q₁ s = (3 * l₀ s * P.q₀) * 2 ^ s := by
  rw [q₁_def, towerDeg_def]
  ac_rfl

/-- The unit represented by `1 + 3 · l₀ s · q₀` modulo `q₁ s`. -/
def towerUnit (s : ℕ) : (ZMod (P.q₁ s))ˣ :=
  ZMod.unitOfCoprime (1 + 3 * l₀ s * P.q₀) (by
    rw [P.q₁_eq_base_mul_two_pow]
    have hbase : (1 + 3 * l₀ s * P.q₀).Coprime (3 * l₀ s * P.q₀) := by
      simp
    have h₂ : 2 ∣ 3 * l₀ s * P.q₀ := dvd_mul_of_dvd_right P.two_dvd_q₀ _
    exact hbase.mul_right ((hbase.of_dvd_right h₂).pow_right s))

/-- The residue underlying the tower unit. -/
@[simp] theorem coe_towerUnit (s : ℕ) :
    (P.towerUnit s : ZMod (P.q₁ s)) = 1 + (3 * l₀ s * P.q₀ : ℕ) := by
  simp [towerUnit]

/-- The tower unit generates a cyclic subgroup of order `2 ^ s`. -/
@[simp] theorem orderOf_towerUnit (s : ℕ) : orderOf (P.towerUnit s) = 2 ^ s := by
  rw [← orderOf_units, P.coe_towerUnit, P.q₁_eq_base_mul_two_pow]
  exact ZMod.orderOf_one_add_natCast_mul_two_pow
    (by have := P.q₀_pos; rw [l₀_def]; positivity)
    (dvd_mul_of_dvd_right ((by norm_num : 4 ∣ 18480).trans P.dvd_q₀) _) s

/-- Among the divisors of `q₁ s`, the tower unit reduces to `1` exactly at the divisors of
`3 · l₀ s · q₀`. -/
@[simp] theorem unitsMap_towerUnit_eq_one_iff {s n : ℕ} (hd : n ∣ P.q₁ s) :
    ZMod.unitsMap hd (P.towerUnit s) = 1 ↔ n ∣ 3 * l₀ s * P.q₀ := by
  rw [Units.ext_iff, ZMod.unitsMap_val, coe_towerUnit, Units.val_one, ZMod.cast_add hd,
    ZMod.cast_one hd, ZMod.cast_natCast hd, add_eq_left, ZMod.natCast_eq_zero_iff]

/-- Distinct exponents below `2 ^ s` give distinct labels `-g ^ e` in the tower. -/
theorem injOn_neg_pow_towerUnit (s : ℕ) :
    (Set.Iio (2 ^ s)).InjOn (fun e : ℕ ↦ -(P.towerUnit s ^ e)) := by
  intro e he f hf h
  exact pow_injOn_Iio_orderOf (by simpa using he) (by simpa using hf) (neg_injective h)

/-- The labels `-g ^ e` reduce to `-1` at every divisor of `3 · l₀ s · q₀`, including `q₀`. -/
@[simp] theorem unitsMap_neg_pow_towerUnit {s n : ℕ} (h : n ∣ 3 * l₀ s * P.q₀)
    (hd : n ∣ P.q₁ s) (e : ℕ) : ZMod.unitsMap hd (-(P.towerUnit s ^ e)) = -1 := by
  rw [ZMod.unitsMap_def, Units.map_neg, ← ZMod.unitsMap_def, map_pow,
    (P.unitsMap_towerUnit_eq_one_iff hd).mpr h, one_pow]

end TauCeti.OneSidedBound.Parameters
