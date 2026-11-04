/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Detection
import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Double

/-!
# Examples of Montgomery stage-1 detection

The raw pair `(21, 25)` modulo `35` represents infinity modulo `5`, but not modulo `7`.
The distinguished point of order two over `ZMod 5` is annihilated by the stage-1 bound
`Nat.lcmUpto 2 = 2`, whereas `(1, 3)` on `y² = x³ + x` over `ZMod 7` has additive order `4`
(whose prime factor `2` is at most `3`, yet `4 ∤ Nat.lcmUpto 3 = 6`), so stage-1 detection at
`B₁ = 2` certifies a proper factor. Doubling `(21, 25)` once more modulo `35` gives `(9, 0)`:
at `m = 4` (or `B₁ = 4`, `Nat.lcmUpto 4 = 12`) both primes are annihilated and `gcd(0, 35) = 35`
is inconclusive. The remaining examples separate the three gcd outcomes and record a proper gcd
for a prime-power modulus.
-/

public section

namespace TauCeti.Montgomery

open WeierstrassCurve

local instance detectionPrimeFive : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance detectionPrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem nonsingular_one_three :
    (model (0 : ZMod 7) 1).toAffine.Nonsingular 1 3 := by
  simp only [Affine.nonsingular_iff, Affine.equation_iff, model_a₁, model_a₂, model_a₃,
    model_a₄, model_a₆]
  decide

private noncomputable def pointSeven : (model (0 : ZMod 7) 1).toAffine.Point :=
  .some 1 3 nonsingular_one_three

private theorem pointSeven_double : pointSeven + pointSeven = twoTorsionPoint 0 (by decide) :=
  (add_self_eq_twoTorsionPoint_iff (by decide) nonsingular_one_three).mpr (by decide)

private theorem four_pointSeven : (4 : ℕ) • pointSeven = 0 := by
  have h4 : (4 : ℕ) = 2 * 2 := rfl
  simp only [h4, mul_nsmul, two_nsmul, pointSeven_double, twoTorsionPoint_add_self]

private theorem addOrderOf_pointSeven : addOrderOf pointSeven = 4 := by
  have hdvd : addOrderOf pointSeven ∣ 4 := addOrderOf_dvd_iff_nsmul_eq_zero.mpr four_pointSeven
  have hle : addOrderOf pointSeven ≤ 4 := Nat.le_of_dvd (by decide) hdvd
  have hpos : 0 < addOrderOf pointSeven :=
    addOrderOf_pos_iff.mpr (isOfFinAddOrder_of_finite pointSeven)
  have hnot2 : ¬ addOrderOf pointSeven ∣ 2 := by
    rw [addOrderOf_dvd_iff_nsmul_eq_zero, two_nsmul, pointSeven_double]
    exact twoTorsionPoint_ne_zero 0 (by decide)
  interval_cases addOrderOf pointSeven <;> simp_all

-- The reduced pair is genuinely nonzero and represents infinity.
example : (Pair.mk 21 25 : Pair (ZMod 35)).map
    (ZMod.castHom (by norm_num : 5 ∣ 35) (ZMod 5)) = ⟨1, 0⟩ := by
  ext <;> simp only [Pair.map_x, Pair.map_z] <;> decide

-- Stage-1 detection at B₁ = 2 (M(2) = 2): the two-torsion point over ZMod 5 has order 2 ≤ 2.
example : 5 ∣ Nat.gcd (25 : ZMod 35).val 35 := by
  apply prime_dvd_gcd_of_addOrderOf_le (n := 35) (p := 5) (A := 0) (B := 1) (B₁ := 2)
    (by decide) (twoTorsionPoint 0 (by decide)) ⟨21, 25⟩ (by simp)
  rw [Nat.lcmUpto_two, two_nsmul, twoTorsionPoint_add_self, coordinates_zero, Pair.cross_def]
  simp only [Pair.map_x, Pair.map_z]
  decide

-- Nonvanishing at 7 upgrades stage-1 detection at B₁ = 2 to a proper factor certificate.
example : 1 < Nat.gcd (25 : ZMod 35).val 35 ∧ Nat.gcd (25 : ZMod 35).val 35 < 35 := by
  refine one_lt_gcd_and_gcd_lt_of_isPrimePow_dvd_addOrderOf_le
    (n := 35) (p := 5) (A := 0) (B := 1) (B₁ := 2)
    (by decide) (twoTorsionPoint 0 (by decide)) ⟨21, 25⟩ ?_ ?_ (q := 7) (by decide) (by decide)
  · intro q _ hq
    rw [addOrderOf_twoTorsionPoint 0 (by decide)] at hq
    exact Nat.le_of_dvd (by decide) hq
  · rw [Nat.lcmUpto_two, two_nsmul, twoTorsionPoint_add_self, coordinates_zero, Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide

-- Over ZMod 7, (1, 3) has order 4: its only prime divisor is 2 ≤ 3, yet neither M(2) = 2 nor
-- M(3) = 6 annihilates it, whereas M(4) = 12 does.
example : ¬ addOrderOf pointSeven ∣ Nat.lcmUpto 2 ∧
    ¬ addOrderOf pointSeven ∣ Nat.lcmUpto 3 ∧
    addOrderOf pointSeven ∣ Nat.lcmUpto 4 := by
  rw [addOrderOf_pointSeven]
  decide

-- Doubling (21, 25) again modulo 35 gives (9, 0): at B₁ = 4 both primes 5 and 7 are annihilated,
-- producing the inconclusive outcome gcd(0, 35) = 35.
example : double (2 : ZMod 35) 4 ⟨21, 25⟩ = ⟨9, 0⟩ ∧
    5 ∣ Nat.gcd (0 : ZMod 35).val 35 ∧
    7 ∣ Nat.gcd (0 : ZMod 35).val 35 ∧
    Nat.gcd (0 : ZMod 35).val 35 = 35 := by
  refine ⟨by ext <;> norm_num [double_x, double_z] <;> decide, ?_, ?_, by decide⟩
  · apply prime_dvd_gcd_of_addOrderOf_le (n := 35) (p := 5) (A := 0) (B := 1) (B₁ := 4)
      (by decide) (twoTorsionPoint 0 (by decide)) ⟨9, 0⟩ (by simp)
    have h12 : (4 : ℕ).lcmUpto • twoTorsionPoint (B := (1 : ZMod 5)) 0 (by decide) = 0 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mp (by rw [addOrderOf_twoTorsionPoint]; decide)
    rw [h12, coordinates_zero, Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide
  · apply prime_dvd_gcd_of_addOrderOf_le (n := 35) (p := 7) (A := 0) (B := 1) (B₁ := 4)
      (by decide) pointSeven ⟨9, 0⟩ (by rw [addOrderOf_pointSeven])
    have h12 : (4 : ℕ).lcmUpto • pointSeven = 0 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mp (by rw [addOrderOf_pointSeven]; decide)
    rw [h12, coordinates_zero, Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide

-- The three gcd outcomes: no factor, a proper factor, and total annihilation.
example : Nat.gcd (1 : ZMod 35).val 35 = 1 ∧
    Nat.gcd (25 : ZMod 35).val 35 = 5 ∧ Nat.gcd (0 : ZMod 35).val 35 = 35 := by
  decide

-- Proper prime-power gcds do not require two distinct prime divisors.
example : Nat.gcd (3 : ZMod 9).val 9 = 3 ∧
    ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3) (3 : ZMod 9) =
      ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3) (0 : ZMod 9) := by
  decide

-- The gcd/reduction bridge also includes modulus zero and negative integers.
example : 5 ∣ Nat.gcd (-15 : ZMod 0).val 0 := by
  rw [ZMod.dvd_gcd_val_iff_castHom_eq_zero _ (dvd_zero 5)]
  decide

end TauCeti.Montgomery
