/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.StageTwo.Basic
import TauCeti.Examples.AlgebraicGeometry.EllipticCurve.Montgomery.Basic
import TauCeti.Examples.AlgebraicGeometry.EllipticCurve.Montgomery.CurveX3AddX

/-!
# Examples of Montgomery stage-2 detection

The point `P = (1, 4)` on `y² = x³ + x` over `𝔽₇` has order four.
For `M = 2`, the point `Q = [M]P` is nonzero, so annihilation has not occurred in stage one,
but `q = 2` annihilates `Q`. Representatives modulo `35` of the giant and baby steps
then give cross-difference gcd `7`. The examples cover a zero baby step, a positive baby
step, the minus sign, independently scaled representatives, and a zero reduction.

Conversely, for `Q₇ = (3, 3)` of order `8` on `y² = x³ + x` over `𝔽₇` and `(m, j) = (3, 1)`,
neither `[2]Q₇` nor `[4]Q₇` vanishes, so `prime_dvd_gcd_cross_iff_zsmul_eq_zero` shows that `7`
does not divide the cross-difference gcd of nonzero representatives `(33, 1)` and `(3, 1)` modulo
`35`. Modulo `5`, the same pairs represent `[3]Q₅` and `[1]Q₅` for `Q₅ = (3, 0)` of order `2`,
where `[4]Q₅ = 0`, and `one_lt_gcd_cross_and_gcd_cross_lt_of_zsmul_eq_zero_of_ne_zero` certifies
that `gcd((33 · 1 - 3 · 1), 35) = 5` is a proper factor of `35`.
-/

public section

namespace TauCeti.Montgomery

open TauCeti.Examples.Montgomery TauCeti.Examples.Montgomery.CurveX3AddX WeierstrassCurve

local instance stageTwoPrimeFive : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance stageTwoPrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem pointOneFourSeven_double :
    pointOneFourSeven + pointOneFourSeven = twoTorsionPoint 0 (by decide) :=
  (add_self_eq_twoTorsionPoint_iff (by decide) nonsingular_one_four_seven).mpr (by decide)

private theorem four_pointOneFourSeven : (4 : ℕ) • pointOneFourSeven = 0 := by
  rw [show (4 : ℕ) = 2 * 2 by decide]
  simp only [mul_nsmul, two_nsmul, pointOneFourSeven_double, twoTorsionPoint_add_self]

-- Stage one does not annihilate this point, whereas multiplying by M*q does.
example : (2 : ℕ) • pointOneFourSeven ≠ 0 ∧ addOrderOf pointOneFourSeven ∣ 2 * 2 := by
  refine ⟨?_, addOrderOf_dvd_iff_nsmul_eq_zero.mpr four_pointOneFourSeven⟩
  rw [two_nsmul, pointOneFourSeven_double]
  exact twoTorsionPoint_ne_zero 0 (by decide)

-- q = 1*2 + 0: both steps are infinity, with different nonzero representatives.
example : 7 ∣ Nat.gcd ((⟨9, 7⟩ : Pair (ZMod 35)).cross ⟨2, 0⟩).val 35 := by
  apply prime_dvd_gcd_cross_of_addOrderOf_dvd_mul (p := 7) (A := 0) (B := 1)
    (M := 2) (q := 2) (i := 1) (w := 2) (j := 0) (by decide) pointOneFourSeven
    ⟨9, 7⟩ ⟨2, 0⟩ (addOrderOf_dvd_iff_nsmul_eq_zero.mpr four_pointOneFourSeven) (.inl (by norm_num))
  · norm_num only [one_mul, two_zsmul, two_nsmul, pointOneFourSeven_double,
      twoTorsionPoint_add_self, coordinates_zero, Pair.cross_def, Pair.map_x, Pair.map_z]
    decide
  · simp only [zero_zsmul, coordinates_zero, Pair.cross_def, Pair.map_x, Pair.map_z]
    decide

-- q = 1*4 - 2: the minus sign gives a positive baby step (the midpoint of the interval).
example : 7 ∣ Nat.gcd ((⟨1, 7⟩ : Pair (ZMod 35)).cross ⟨2, 0⟩).val 35 := by
  apply prime_dvd_gcd_cross_of_addOrderOf_dvd_mul (p := 7) (A := 0) (B := 1)
    (M := 2) (q := 2) (i := 1) (w := 4) (j := 2) (by decide) pointOneFourSeven
    ⟨1, 7⟩ ⟨2, 0⟩ (addOrderOf_dvd_iff_nsmul_eq_zero.mpr four_pointOneFourSeven) (.inr (by norm_num))
  · rw [one_mul, two_nsmul, pointOneFourSeven_double]
    have hfour : (4 : ℤ) • twoTorsionPoint (0 : ZMod 7) (by decide : (1 : ZMod 7) ≠ 0) = 0 := by
      rw [show (4 : ℤ) = 2 + 2 by decide, add_zsmul, two_zsmul, twoTorsionPoint_add_self]
      simp
    rw [hfour, coordinates_zero, Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide
  · rw [two_nsmul, pointOneFourSeven_double, two_zsmul, twoTorsionPoint_add_self, coordinates_zero,
      Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide

-- The detected gcd is proper; neither representative reduces to zero modulo 7.
example : Nat.gcd ((⟨9, 7⟩ : Pair (ZMod 35)).cross ⟨2, 0⟩).val 35 = 7 ∧
    (⟨9, 7⟩ : Pair (ZMod 35)).map (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7)) ≠ 0 ∧
    (⟨2, 0⟩ : Pair (ZMod 35)).map (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7)) ≠ 0 := by
  simp only [Pair.cross_def, Pair.ne_zero_iff, Pair.map_x, Pair.map_z]
  decide

-- Zero reductions are allowed, but may give the inconclusive gcd equal to n.
example : 7 ∣ Nat.gcd ((0 : Pair (ZMod 35)).cross 0).val 35 := by
  apply prime_dvd_gcd_cross_of_zsmul_eq_zero (p := 7) (A := 0) (B := 1)
    (q := 4) (m := 3) (j := 1) (by decide) pointOneFourSeven 0 0
    ((natCast_zsmul pointOneFourSeven 4).trans four_pointOneFourSeven) (.inl (by norm_num))
  all_goals simp

-- The nearest-multiple theorem applies directly, without choosing a decomposition by hand.
example : ∃ i : ℤ, 2 * |(2 : ℤ) - i * 6| ≤ 6 ∧
    ∀ R S : Pair (ZMod 35),
      (R.map (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7))).cross
        (coordinates 0 1 ((i * 6) • ((2 : ℕ) • pointOneFourSeven))) = 0 →
      (S.map (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7))).cross
        (coordinates 0 1 (|(2 : ℤ) - i * 6| • ((2 : ℕ) • pointOneFourSeven))) = 0 →
      7 ∣ Nat.gcd (R.cross S).val 35 :=
  exists_two_mul_abs_sub_mul_le_and_prime_dvd_gcd_cross (by decide) pointOneFourSeven
    (addOrderOf_dvd_iff_nsmul_eq_zero.mpr four_pointOneFourSeven) (by norm_num)

private theorem nonsingular_three_zero_five :
    (model (0 : ZMod 5) 1).toAffine.Nonsingular 3 0 := by
  simp only [Affine.nonsingular_iff, Affine.equation_iff, model_a₁, model_a₂, model_a₃,
    model_a₄, model_a₆]
  decide

private noncomputable def pointFive : (model (0 : ZMod 5) 1).toAffine.Point :=
  .some 3 0 nonsingular_three_zero_five

private theorem three_pointFive : (3 : ℕ) • pointFive = pointFive := by
  have h3 : (3 : ℕ) = 2 + 1 := rfl
  rw [h3, add_nsmul, two_nsmul_eq_zero_five, zero_add, one_nsmul]

private theorem four_pointFive : (4 : ℤ) • pointFive = 0 := by
  have h4 : (4 : ℤ) = (2 * 2 : ℕ) := rfl
  rw [h4, natCast_zsmul, mul_nsmul, two_nsmul_eq_zero_five]

-- Converse direction of stage-2 detection: for `Q₇ = (3, 3)` of order `8` over `ZMod 7` and
-- `(m, j) = (3, 1)`, neither `[2]Q₇` nor `[4]Q₇` vanishes, so `7` does not divide the
-- cross-difference gcd of `(33, 1)` and `(3, 1)` modulo `35`.
example : ¬ 7 ∣ Nat.gcd ((⟨33, 1⟩ : Pair (ZMod 35)).cross ⟨3, 1⟩).val 35 := by
  have h3z : (3 : ℤ) = (3 : ℕ) := rfl
  rw [prime_dvd_gcd_cross_iff_zsmul_eq_zero (n := 35) (p := 7) (A := 0) (B := 1)
    (m := 3) (j := 1) (by decide) one_ne_zero pointThreeThreeSeven ⟨33, 1⟩ ⟨3, 1⟩ ?_ ?_ ?_ ?_]
  · refine not_or.mpr ⟨?_, ?_⟩
    · have h2 : (3 - 1 : ℤ) = (2 : ℕ) := rfl
      rw [h2, natCast_zsmul, two_nsmul_pointThreeThreeSeven]
      exact Affine.Point.some_ne_zero _
    · have h4 : (3 + 1 : ℤ) = (4 : ℕ) := rfl
      rw [h4, natCast_zsmul, four_nsmul_pointThreeThreeSeven]
      exact twoTorsionPoint_ne_zero 0 (by decide)
  · rw [Pair.ne_zero_iff]
    simp only [Pair.map_x, Pair.map_z]
    decide
  · rw [Pair.ne_zero_iff]
    simp only [Pair.map_x, Pair.map_z]
    decide
  · rw [h3z, natCast_zsmul, three_nsmul_pointThreeThreeSeven, coordinates_some, Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide
  · rw [one_zsmul, pointThreeThreeSeven, coordinates_some, Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide

-- Combining `[4]Q₅ = 0` modulo `5` with `[2]Q₇ ≠ 0` and `[4]Q₇ ≠ 0` modulo `7` certifies that
-- `gcd(((33, 1).cross (3, 1)).val, 35) = 5` is a proper factor of `35`.
example : 1 < Nat.gcd ((⟨33, 1⟩ : Pair (ZMod 35)).cross ⟨3, 1⟩).val 35 ∧
    Nat.gcd ((⟨33, 1⟩ : Pair (ZMod 35)).cross ⟨3, 1⟩).val 35 < 35 := by
  have h3z : (3 : ℤ) = (3 : ℕ) := rfl
  refine one_lt_gcd_cross_and_gcd_cross_lt_of_zsmul_eq_zero_of_ne_zero
    (n := 35) (p := 5) (A := 0) (B := 1) (q := 4) (m := 3) (j := 1)
    (by decide) pointFive ⟨33, 1⟩ ⟨3, 1⟩ four_pointFive (.inl (by norm_num)) ?_ ?_
    (r := 7) (A' := 0) (B' := 1) (by decide) one_ne_zero pointThreeThreeSeven ?_ ?_ ?_ ?_ ?_ ?_
  · rw [h3z, natCast_zsmul, three_pointFive, pointFive, coordinates_some, Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide
  · rw [one_zsmul, pointFive, coordinates_some, Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide
  · have h2 : (3 - 1 : ℤ) = (2 : ℕ) := rfl
    rw [h2, natCast_zsmul, two_nsmul_pointThreeThreeSeven]
    exact Affine.Point.some_ne_zero _
  · have h4 : (3 + 1 : ℤ) = (4 : ℕ) := rfl
    rw [h4, natCast_zsmul, four_nsmul_pointThreeThreeSeven]
    exact twoTorsionPoint_ne_zero 0 (by decide)
  · rw [Pair.ne_zero_iff]
    simp only [Pair.map_x, Pair.map_z]
    decide
  · rw [Pair.ne_zero_iff]
    simp only [Pair.map_x, Pair.map_z]
    decide
  · rw [h3z, natCast_zsmul, three_nsmul_pointThreeThreeSeven, coordinates_some, Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide
  · rw [one_zsmul, pointThreeThreeSeven, coordinates_some, Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide

-- After stage-1 multiplier `M = 2` on `P = (1, 4)` of order `4` over `ZMod 7`,
-- `prime_dvd_gcd_cross_iff_addOrderOf_dvd_mul` reduces stage-2 divisibility at
-- `(i, w, j) = (1, 1, 0)` (where `[1]([2]P) = (0, 0)` and `[0]([2]P) = ∞`) to `4 ∣ 2 * 1`.
example : ¬ 7 ∣ Nat.gcd ((⟨0, 1⟩ : Pair (ZMod 35)).cross ⟨1, 0⟩).val 35 := by
  have hord : addOrderOf pointOneFourSeven = 4 := by
    refine addOrderOf_eq_prime_pow (p := 2) (n := 1) ?_ four_pointOneFourSeven
    rw [pow_one, two_nsmul, pointOneFourSeven_double]
    exact twoTorsionPoint_ne_zero 0 (by decide)
  rw [prime_dvd_gcd_cross_iff_addOrderOf_dvd_mul (n := 35) (p := 7) (A := 0) (B := 1)
    (M := 2) (i := 1) (w := 1) (j := 0) (by decide) one_ne_zero pointOneFourSeven ⟨0, 1⟩ ⟨1, 0⟩
    ?_ ?_ ?_ ?_, hord]
  · decide
  · rw [Pair.ne_zero_iff]
    simp only [Pair.map_x, Pair.map_z]
    decide
  · rw [Pair.ne_zero_iff]
    simp only [Pair.map_x, Pair.map_z]
    decide
  · rw [one_mul, one_zsmul, two_nsmul, pointOneFourSeven_double, coordinates_twoTorsionPoint,
      Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide
  · rw [zero_zsmul, coordinates_zero, Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide

end TauCeti.Montgomery
