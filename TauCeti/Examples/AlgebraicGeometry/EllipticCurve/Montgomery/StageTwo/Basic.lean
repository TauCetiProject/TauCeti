/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.StageTwo.Basic

/-!
# Examples of Montgomery stage-2 detection

The point `P = (1, 4)` on `y² = x³ + x` over `𝔽₇` has order four.
For `M = 2`, the point `Q = [M]P` is nonzero, so annihilation has not occurred in stage one,
but `q = 2` annihilates `Q`. Representatives modulo `35` of the giant and baby steps
then give cross-difference gcd `7`. The examples cover a zero baby step, a positive baby
step, the minus sign, independently scaled representatives, and a zero reduction.
-/

public section

namespace TauCeti.Montgomery

open WeierstrassCurve

local instance stageTwoPrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem nonsingular_one_four :
    (model (0 : ZMod 7) 1).toAffine.Nonsingular 1 4 := by
  simp only [Affine.nonsingular_iff, Affine.equation_iff, model_a₁, model_a₂, model_a₃,
    model_a₄, model_a₆]
  decide

private noncomputable def point : (model (0 : ZMod 7) 1).toAffine.Point :=
  .some 1 4 nonsingular_one_four

private theorem point_double : point + point = twoTorsionPoint 0 (by decide) := by
  exact (add_self_eq_twoTorsionPoint_iff (by decide) nonsingular_one_four).mpr (by decide)

private theorem four_point : (4 : ℕ) • point = 0 := by
  rw [show (4 : ℕ) = 2 * 2 by decide]
  simp only [mul_nsmul, two_nsmul, point_double, twoTorsionPoint_add_self]

-- Stage one does not annihilate this point, whereas multiplying by M*q does.
example : (2 : ℕ) • point ≠ 0 ∧ addOrderOf point ∣ 2 * 2 := by
  refine ⟨?_, addOrderOf_dvd_iff_nsmul_eq_zero.mpr four_point⟩
  rw [two_nsmul, point_double]
  exact twoTorsionPoint_ne_zero 0 (by decide)

-- q = 1*2 + 0: both steps are infinity, with different nonzero representatives.
example : 7 ∣ Nat.gcd ((⟨9, 7⟩ : Pair (ZMod 35)).cross ⟨2, 0⟩).val 35 := by
  apply prime_dvd_gcd_cross_of_addOrderOf_dvd_mul (p := 7) (A := 0) (B := 1)
    (M := 2) (q := 2) (i := 1) (w := 2) (j := 0) (by decide) point
    ⟨9, 7⟩ ⟨2, 0⟩ (addOrderOf_dvd_iff_nsmul_eq_zero.mpr four_point) (.inl (by norm_num))
  · norm_num only [one_mul, two_zsmul, two_nsmul, point_double, twoTorsionPoint_add_self,
      coordinates_zero, Pair.cross_def, Pair.map_x, Pair.map_z]
    decide
  · simp only [zero_zsmul, coordinates_zero, Pair.cross_def, Pair.map_x, Pair.map_z]
    decide

-- q = 1*4 - 2: the minus sign gives a positive baby step (the midpoint of the interval).
example : 7 ∣ Nat.gcd ((⟨1, 7⟩ : Pair (ZMod 35)).cross ⟨2, 0⟩).val 35 := by
  apply prime_dvd_gcd_cross_of_addOrderOf_dvd_mul (p := 7) (A := 0) (B := 1)
    (M := 2) (q := 2) (i := 1) (w := 4) (j := 2) (by decide) point
    ⟨1, 7⟩ ⟨2, 0⟩ (addOrderOf_dvd_iff_nsmul_eq_zero.mpr four_point) (.inr (by norm_num))
  · rw [one_mul, two_nsmul, point_double]
    have hfour : (4 : ℤ) • twoTorsionPoint (0 : ZMod 7) (by decide : (1 : ZMod 7) ≠ 0) = 0 := by
      rw [show (4 : ℤ) = 2 + 2 by decide, add_zsmul, two_zsmul, twoTorsionPoint_add_self]
      simp
    rw [hfour, coordinates_zero, Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide
  · rw [two_nsmul, point_double, two_zsmul, twoTorsionPoint_add_self, coordinates_zero,
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
    (q := 4) (m := 3) (j := 1) (by decide) point 0 0
    ((natCast_zsmul point 4).trans four_point) (.inl (by norm_num))
  all_goals simp

-- The nearest-multiple theorem applies directly, without choosing a decomposition by hand.
example : ∃ i : ℤ, 2 * |(2 : ℤ) - i * 6| ≤ 6 ∧
    ∀ R S : Pair (ZMod 35),
      (R.map (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7))).cross
        (coordinates 0 1 ((i * 6) • ((2 : ℕ) • point))) = 0 →
      (S.map (ZMod.castHom (by decide : 7 ∣ 35) (ZMod 7))).cross
        (coordinates 0 1 (|(2 : ℤ) - i * 6| • ((2 : ℕ) • point))) = 0 →
      7 ∣ Nat.gcd (R.cross S).val 35 :=
  exists_two_mul_abs_sub_mul_le_and_prime_dvd_gcd_cross (by decide) point
    (addOrderOf_dvd_iff_nsmul_eq_zero.mpr four_point) (by norm_num)

end TauCeti.Montgomery
