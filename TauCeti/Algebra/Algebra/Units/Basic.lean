/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.Ring

/-!
# Central scalar units and quasi-commutation in an algebra

For a commutative semiring `R` and an `R`-algebra `B`, units pushed forward along `algebraMap R B`
are central in `Bˣ`. Consequently, central-unit factors collect cleanly in products of scaled units
(`Units.map_algebraMap_mul_mul_map_algebraMap_mul`), and integer powers inherit central-unit
quasi-commutation `x * y = w • (y * x)` (`Units.zpow_mul_of_map_algebraMap_mul`,
`Units.zpow_mul_zpow_of_map_algebraMap_mul`).
-/

public section

namespace Units

variable {R B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]

/-- Scalar units pushed forward along `algebraMap R B` commute with every unit of `B`. -/
theorem commute_map_algebraMap (w : Rˣ) (x : Bˣ) :
    Commute (Units.map (algebraMap R B) w) x :=
  Units.ext <| Algebra.commutes _ _

/-- Scalar units pushed forward along `algebraMap R B` commute with every unit of `B`. -/
theorem map_algebraMap_mul_comm (w : Rˣ) (x : Bˣ) :
    Units.map (algebraMap R B) w * x = x * Units.map (algebraMap R B) w :=
  commute_map_algebraMap w x

/-- Pull a central scalar unit across a left factor in `Bˣ`. -/
theorem mul_map_algebraMap_mul (w : Rˣ) (x y : Bˣ) :
    x * (Units.map (algebraMap R B) w * y) = Units.map (algebraMap R B) w * (x * y) := by
  rw [← mul_assoc, ← map_algebraMap_mul_comm, mul_assoc]

/-- Combine two adjacent central scalar-unit factors in `Bˣ`. -/
theorem map_algebraMap_mul_map_algebraMap (w₁ w₂ : Rˣ) (x : Bˣ) :
    Units.map (algebraMap R B) w₁ * (Units.map (algebraMap R B) w₂ * x) =
      Units.map (algebraMap R B) (w₁ * w₂) * x := by
  rw [← mul_assoc, ← map_mul]

/-- Multiply two scalar-unit-scaled elements of `Bˣ` by multiplying their scalar and unit parts. -/
theorem map_algebraMap_mul_mul_map_algebraMap_mul (w₁ w₂ : Rˣ) (x y : Bˣ) :
    (Units.map (algebraMap R B) w₁ * x) * (Units.map (algebraMap R B) w₂ * y) =
      Units.map (algebraMap R B) (w₁ * w₂) * (x * y) := by
  rw [mul_assoc, mul_map_algebraMap_mul, map_algebraMap_mul_map_algebraMap]

/-- Integer powers on the left inherit central-unit quasi-commutation `x * y = w • (y * x)`. -/
theorem zpow_mul_of_map_algebraMap_mul {w : Rˣ} {x y : Bˣ}
    (h : x * y = Units.map (algebraMap R B) w * (y * x)) (m : ℤ) :
    x ^ m * y = Units.map (algebraMap R B) (w ^ m) * (y * x ^ m) := by
  let cw : Bˣ := Units.map (algebraMap R B) w
  have hyx : SemiconjBy y x (cw⁻¹ * x) := mul_left_cancel (a := cw) <| by
    rw [← h, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  have hcomm : Commute cw⁻¹ x := by
    rw [← map_inv]
    exact commute_map_algebraMap w⁻¹ x
  have hpow := (hyx.zpow_right m).eq
  rw [hcomm.mul_zpow m, mul_assoc] at hpow
  rw [hpow, ← mul_assoc, ← map_inv, ← map_zpow, inv_zpow', ← map_mul, ← zpow_add,
    add_neg_cancel, zpow_zero, map_one, one_mul]

/-- Integer powers on both sides inherit central-unit quasi-commutation: if
`x * y = w • (y * x)`, then `x ^ m * y ^ n = w ^ (m * n) • (y ^ n * x ^ m)`. -/
theorem zpow_mul_zpow_of_map_algebraMap_mul {w : Rˣ} {x y : Bˣ}
    (h : x * y = Units.map (algebraMap R B) w * (y * x)) (m n : ℤ) :
    x ^ m * y ^ n = Units.map (algebraMap R B) (w ^ (m * n)) * (y ^ n * x ^ m) := by
  have hyx : y * x = Units.map (algebraMap R B) (w ^ (-1 : ℤ)) * (x * y) :=
    mul_left_cancel (a := Units.map (algebraMap R B) w) <| by
      rw [← h, map_algebraMap_mul_map_algebraMap, zpow_neg_one, mul_inv_cancel, map_one, one_mul]
  have hyn : x * y ^ n = Units.map (algebraMap R B) (w ^ n) * (y ^ n * x) :=
    mul_left_cancel (a := Units.map (algebraMap R B) ((w ^ (-1 : ℤ)) ^ n)) <| by
      rw [← zpow_mul_of_map_algebraMap_mul hyx n, map_algebraMap_mul_map_algebraMap, ← zpow_mul,
        ← zpow_add, (by ring : -1 * n + n = 0), zpow_zero, map_one, one_mul]
  rw [zpow_mul_of_map_algebraMap_mul hyn m, ← zpow_mul, mul_comm n m]

end Units
