/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic

/-!
# Central scalar units and quasi-commutation in an algebra

For a commutative semiring `R` and an `R`-algebra `B`, units pushed forward along `algebraMap R B`
are central in `Bˣ`. Consequently, central-unit factors collect cleanly in products of scaled units
(`Units.map_algebraMap_mul_mul_map_algebraMap_mul`), integer powers inherit central-unit
quasi-commutation `x * y = w • (y * x)` (`Units.zpow_mul_of_map_algebraMap_mul`,
`Units.zpow_mul_zpow_of_map_algebraMap_mul`), and inverse conjugation scales quasi-commuting
elements by `w⁻¹` (`Units.inv_mul_mul_of_mul_eq_algebraMap_mul`).
-/

public section

namespace Units

variable {R B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]

/-- Scalar units pushed forward along `algebraMap R B` commute with every unit of `B`. -/
theorem commute_map_algebraMap (w : Rˣ) (x : Bˣ) :
    Commute (Units.map (algebraMap R B) w) x :=
  Units.ext <| Algebra.commutes _ _

/-- Pull a central scalar unit across a left factor in `Bˣ`. -/
theorem mul_map_algebraMap_mul (w : Rˣ) (x y : Bˣ) :
    x * (Units.map (algebraMap R B) w * y) = Units.map (algebraMap R B) w * (x * y) := by
  rw [← mul_assoc, ← (commute_map_algebraMap w x).eq, mul_assoc]

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

/-- Moving a central scalar unit `Units.map (algebraMap R B) w` across `=` inverts `w`. -/
theorem eq_map_algebraMap_inv_mul_iff (w : Rˣ) (x y : Bˣ) :
    x = Units.map (algebraMap R B) w⁻¹ * y ↔ Units.map (algebraMap R B) w * x = y :=
  ⟨fun h ↦ by rw [h, map_algebraMap_mul_map_algebraMap, mul_inv_cancel, map_one, one_mul],
   fun h ↦ by rw [← h, map_algebraMap_mul_map_algebraMap, inv_mul_cancel, map_one, one_mul]⟩

/-- Moving a central scalar unit power `u ^ n` across `=` negates the exponent. -/
theorem eq_map_algebraMap_zpow_neg_mul_iff (u : Rˣ) (n : ℤ) (x y : Bˣ) :
    x = Units.map (algebraMap R B) (u ^ (-n)) * y ↔
      Units.map (algebraMap R B) (u ^ n) * x = y := by
  rw [zpow_neg, eq_map_algebraMap_inv_mul_iff]

/-- Integer powers on the left inherit central-unit quasi-commutation `x * y = w • (y * x)`. -/
theorem zpow_mul_of_map_algebraMap_mul {w : Rˣ} {x y : Bˣ}
    (h : x * y = Units.map (algebraMap R B) w * (y * x)) (m : ℤ) :
    x ^ m * y = Units.map (algebraMap R B) (w ^ m) * (y * x ^ m) := by
  let cw : Bˣ := Units.map (algebraMap R B) w
  have hyx : SemiconjBy y x (cw⁻¹ * x) :=
    ((eq_map_algebraMap_inv_mul_iff w (y * x) (x * y)).mpr h.symm).trans (mul_assoc _ _ _).symm
  have hcomm : Commute cw⁻¹ x := by
    rw [← map_inv]
    exact commute_map_algebraMap w⁻¹ x
  have hpow := (hyx.zpow_right m).eq
  rw [hcomm.mul_zpow m, mul_assoc, ← map_inv, ← map_zpow, inv_zpow] at hpow
  exact ((eq_map_algebraMap_inv_mul_iff (w ^ m) (y * x ^ m) (x ^ m * y)).mp hpow).symm

/-- Integer powers on both sides inherit central-unit quasi-commutation: if
`x * y = w • (y * x)`, then `x ^ m * y ^ n = w ^ (m * n) • (y ^ n * x ^ m)`. -/
theorem zpow_mul_zpow_of_map_algebraMap_mul {w : Rˣ} {x y : Bˣ}
    (h : x * y = Units.map (algebraMap R B) w * (y * x)) (m n : ℤ) :
    x ^ m * y ^ n = Units.map (algebraMap R B) (w ^ (m * n)) * (y ^ n * x ^ m) := by
  have hyx : y * x = Units.map (algebraMap R B) w⁻¹ * (x * y) :=
    (eq_map_algebraMap_inv_mul_iff w _ _).mpr h.symm
  have hyn' := zpow_mul_of_map_algebraMap_mul hyx n
  rw [inv_zpow] at hyn'
  have hyn : x * y ^ n = Units.map (algebraMap R B) (w ^ n) * (y ^ n * x) :=
    ((eq_map_algebraMap_inv_mul_iff (w ^ n) (y ^ n * x) (x * y ^ n)).mp hyn').symm
  rw [zpow_mul_of_map_algebraMap_mul hyn m, ← zpow_mul, mul_comm n m]

/-- If `x : Bˣ` quasi-commutes past `z : B` by a central scalar unit `w : Rˣ`, then inverse
conjugation `x⁻¹ * z * x` scales `z` by `w⁻¹`. -/
theorem inv_mul_mul_of_mul_eq_algebraMap_mul {w : Rˣ} {x : Bˣ} {z : B}
    (h : (x : B) * z = algebraMap R B w * (z * (x : B))) :
    ((x⁻¹ : Bˣ) : B) * z * (x : B) = algebraMap R B (w⁻¹ : Rˣ) * z := by
  calc
    ((x⁻¹ : Bˣ) : B) * z * (x : B)
      = (algebraMap R B (w⁻¹ : Rˣ) * algebraMap R B w) *
          (((x⁻¹ : Bˣ) : B) * z * (x : B)) := by
        rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one, one_mul]
    _ = algebraMap R B (w⁻¹ : Rˣ) *
          ((algebraMap R B w * ((x⁻¹ : Bˣ) : B)) * (z * (x : B))) := by
        simp only [mul_assoc]
    _ = algebraMap R B (w⁻¹ : Rˣ) * (((x⁻¹ : Bˣ) : B) * ((x : B) * z)) := by
        rw [Algebra.commutes (w : R), mul_assoc ((x⁻¹ : Bˣ) : B), h]
    _ = algebraMap R B (w⁻¹ : Rˣ) * z := by
        rw [x.inv_mul_cancel_left]

end Units
